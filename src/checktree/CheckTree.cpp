/**
 * @file CheckTree.cpp
 * @brief Implementation of CheckTree class
 */

#include "CheckTree.h"

#include "diff/DiffGenerator.h"
#include "diff/DiffParser.h"
#include "refactor/HunkRefactorer.h"
#include "utils/FileUtil.h"
#include "utils/GitWrapper.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <algorithm>
#include <future>

namespace elomig {
namespace checktree {

	CheckTree::CheckTree() : m_stay( false ), m_debugMode( false ), m_createMode( false ), m_threadCount( std::thread::hardware_concurrency() ) {
		// Initialize thread pool
		if ( m_threadCount > 1 ) {
			m_threadPool = std::make_unique< ThreadPool >( m_threadCount );
		}
	}

	CheckTree::~CheckTree() {
		// Restore upstream if needed
		if ( !m_stay && !m_previousCommit.empty() ) {
			GitWrapper git( m_upstreamPath );
			if ( git.isValid() ) {
				LOG_DEBUG( "Restoring upstream to %s", m_previousCommit.c_str() );
				git.checkout( m_previousCommit );
			}
		}
	}

	bool CheckTree::resolveSourceDir() {
		if ( m_sourcePath.empty() ) {
			// Default to ./src or current directory
			if ( utils::isDirectory( "src" ) ) {
				m_resolvedSource = "src";
			} else {
				m_resolvedSource = ".";
			}
		} else {
			// Check if path ends with /src or contains src subdirectory
			if ( utils::endsWith( m_sourcePath, "/src" ) ) {
				m_resolvedSource = m_sourcePath;
			} else if ( utils::isDirectory( m_sourcePath + "/src" ) ) {
				m_resolvedSource = m_sourcePath + "/src";
			} else {
				m_resolvedSource = m_sourcePath;
			}
		}

		LOG_DEBUG( "Resolved source directory: %s", m_resolvedSource.c_str() );
		return utils::isDirectory( m_resolvedSource );
	}

	bool CheckTree::generateFileList() {
		m_allFiles.clear();

		if ( !m_files.empty() ) {
			// Use provided files
			m_allFiles = m_files;

			// Verify files exist (unless create mode)
			for ( auto const& file : m_allFiles ) {
				std::string fullPath = m_resolvedSource + "/" + file;
				if ( !utils::fileExists( fullPath ) && !m_createMode ) {
					LOG_WARNING( "File not found: %s", file.c_str() );
				}
			}
		} else {
			// Scan directories
			static std::vector< std::string > const dirs      = { "doc", "docs", "factory", "m4", "man", "po", "shell-completion", "src", "tools" };

			static std::vector< std::string > const rootFiles = {
				".gitignore", ".mailmap", "configure", "meson.build", "meson.version", "meson_options.txt", "TODO"
			};

			for ( auto const& dir : dirs ) {
				std::string dirPath = m_resolvedSource + "/" + dir;
				if ( utils::isDirectory( dirPath ) ) {
					auto files = utils::findFiles( dirPath, { "*" } );
					for ( auto const& file : files ) {
						// Skip .pwx files and man/rules
						if ( utils::endsWith( file, ".pwx" ) || file.find( "man/rules/" ) != std::string::npos ) {
							continue;
						}

						// Make relative to source
						std::string relPath = utils::getRelativePath( file, m_resolvedSource );
						m_allFiles.push_back( relPath );
					}
				}
			}

			// Add root files
			for ( auto const& rootFile : rootFiles ) {
				std::string fullPath = m_resolvedSource + "/" + rootFile;
				if ( utils::fileExists( fullPath ) ) {
					m_allFiles.push_back( rootFile );
				}
			}
		}

		LOG_DEBUG( "Found %zu files to process", m_allFiles.size() );
		return !m_allFiles.empty();
	}

	bool CheckTree::checkoutUpstream() {
		if ( m_commit.empty() ) {
			return true; // No checkout needed
		}

		GitWrapper git( m_upstreamPath );
		if ( !git.isValid() ) {
			LOG_ERROR( "Failed to open upstream repository" );
			return false;
		}

		// Save current commit
		m_previousCommit = git.getHeadCommit();

		// Get target commit
		std::string targetCommit = git.getShortHash( m_commit );
		if ( targetCommit.empty() ) {
			LOG_ERROR( "Failed to resolve commit: %s", m_commit.c_str() );
			return false;
		}

		// Check if already at target
		std::string currentCommit = git.getHeadCommit();
		if ( currentCommit == targetCommit ) {
			LOG_DEBUG( "Already at commit %s", targetCommit.c_str() );
			return true;
		}

		// Checkout target
		LOG_STATUS( "Checking out %s in upstream", targetCommit.c_str() );
		return git.checkout( m_commit );
	}

	bool CheckTree::processFile( std::string const& filePart ) {
		LOG_DEBUG( "Processing file: %s", filePart.c_str() );

		// Create FileDiff object
		auto fileDiff = std::make_shared< FileDiff >( filePart );

		// Build source and target paths
		std::string sourcePath = m_resolvedSource + "/" + filePart;
		std::string targetPath = filePart;

		// Replace elogind with systemd in target path
		targetPath = utils::replaceAll( targetPath, "elogind", "systemd" );

		fileDiff->setSourcePath( sourcePath );
		fileDiff->setTargetPath( targetPath );

		// Determine file type
		std::string kind = FileDiff::getFileKind( filePart );
		fileDiff->setIsShell( kind == "shell" );
		fileDiff->setIsXML( kind == "xml" );

		// Check if target exists
		std::string fullTargetPath = m_upstreamPath + "/" + targetPath;
		if ( !utils::fileExists( fullTargetPath ) ) {
			// Try alternative name resolution
			// TODO: Implement change_find_alt_text logic

			LOG_STATUS( "%s: only here", filePart.c_str() );
			m_onlyHere.push_back( filePart );
			return false;
		}

		fileDiff->setTargetPath( fullTargetPath );

		// Generate diff
		if ( !generateDiff( fileDiff ) ) {
			LOG_STATUS( "%s: same", filePart.c_str() );
			return false;
		}

		// Refactor hunks
		if ( !refactorHunks( fileDiff ) ) {
			LOG_WARNING( "Failed to refactor hunks for %s", filePart.c_str() );
		}

		// Build output and write patch
		if ( fileDiff->hasUsefulChanges() ) {
			fileDiff->buildOutput();
			writePatch( fileDiff );

			size_t usefulCount = fileDiff->countUsefulHunks();
			LOG_STATUS( "%s: %zu Hunk%s", filePart.c_str(), usefulCount, usefulCount > 1 ? "s" : "" );
		} else {
			LOG_STATUS( "%s: clean", filePart.c_str() );
		}

		m_fileDiffs.push_back( fileDiff );
		return true;
	}

	bool CheckTree::processFilesParallel( std::vector< std::string > const& files ) {
		if ( files.empty() || !m_threadPool ) {
			// Fall back to sequential processing
			for ( auto const& file : files ) {
				processFile( file );
			}
			return true;
		}

		LOG_DEBUG( "Processing %zu files in parallel with %zu threads", files.size(), m_threadPool->threadCount() );

		// Process files in parallel using thread pool
		std::vector< std::future< bool > > futures;

		for ( auto const& file : files ) {
			auto future = m_threadPool->enqueue( [this, file]() { return this->processFile( file ); } );
			futures.push_back( std::move( future ) );
		}

		// Wait for all files to complete and collect results
		for ( auto& future : futures ) {
			try {
				future.wait();
			} catch ( std::exception const& e ) {
				LOG_ERROR( "Error processing file: %s", e.what() );
			}
		}

		return true;
	}

	bool CheckTree::generateDiff( std::shared_ptr< FileDiff > fileDiff ) {
		DiffGenerator generator;

		std::string   diffOutput = generator.generateUnifiedDiff( fileDiff->sourcePath(), fileDiff->targetPath(), fileDiff->part() );

		if ( diffOutput.empty() ) {
			return false; // No differences
		}

		// Parse diff
		DiffParser parser;
		if ( !parser.parse( diffOutput, fileDiff ) ) {
			LOG_ERROR( "Failed to parse diff for %s", fileDiff->part().c_str() );
			return false;
		}

		return fileDiff->hunkCount() > 0;
	}

	bool CheckTree::refactorHunks( std::shared_ptr< FileDiff > fileDiff ) {
		HunkRefactorer refactorer;

		// Prepare file if needed (shell/XML)
		if ( fileDiff->isShell() || fileDiff->isXML() ) {
			fileDiff->setIsPrepared( true );
			// TODO: Implement prepare_shell/prepare_xml
		}

		// Process each hunk
		for ( auto& hunk : fileDiff->hunks() ) {
			if ( !hunk ) {
				continue;
			}

			// Run all refactoring passes
			refactorer.processHunk( hunk, fileDiff );
		}

		// Finalize
		refactorer.finishHunks( fileDiff );

		return true;
	}

	bool CheckTree::writePatch( std::shared_ptr< FileDiff > fileDiff ) {
		// Build patch path
		std::string patchName = utils::replaceAll( fileDiff->part(), "/", "_" );
		std::string patchPath = "patches/" + patchName + ".patch";

		// Ensure patches directory exists
		utils::createDirectory( "patches" );

		// Write patch
		if ( utils::writeFile( patchPath, fileDiff->output() ) ) {
			LOG_DEBUG( "Wrote patch: %s", patchPath.c_str() );
			return true;
		} else {
			LOG_ERROR( "Failed to write patch: %s", patchPath.c_str() );
			return false;
		}
	}

	bool CheckTree::run() {
		LOG_DEBUG( "Starting check tree operation" );

		// Resolve source directory
		if ( !resolveSourceDir() ) {
			LOG_ERROR( "Invalid source directory" );
			return false;
		}

		// Generate file list
		if ( !generateFileList() ) {
			LOG_ERROR( "No files to process" );
			return false;
		}

		// Checkout upstream commit
		if ( !checkoutUpstream() ) {
			return false;
		}

		// Process files in parallel
		processFilesParallel( m_allFiles );

		// Report files only in local tree
		if ( !m_onlyHere.empty() ) {
			LOG_STATUS( "\n%zu file(s) only found in local tree:", m_onlyHere.size() );
			for ( auto const& file : m_onlyHere ) {
				LOG_STATUS( "  %s", file.c_str() );
			}
		}

		return true;
	}

} // namespace checktree
} // namespace elomig
