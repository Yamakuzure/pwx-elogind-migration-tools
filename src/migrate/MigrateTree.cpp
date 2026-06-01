/**
 * @file MigrateTree.cpp
 * @brief Implementation of migrate tree functionality
 */

#include "MigrateTree.h"

#include "CommitDiscovery.h"
#include "CommitFile.h"
#include "PatchApplier.h"
#include "PatchGenerator.h"
#include "utils/FileUtil.h"
#include "utils/GitWrapper.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <algorithm>
#include <filesystem>

namespace elomig {
namespace migrate {

	MigrateTree::MigrateTree() : m_advance( false ), m_debugMode( false ), m_commitsRead( false ) {
		// Initialize components
		m_commitDiscovery = std::make_unique< CommitDiscovery >();
		m_patchGenerator  = std::make_unique< PatchGenerator >();
		m_patchApplier    = std::make_unique< PatchApplier >();
		m_commitFile      = std::make_unique< CommitFile >();

		// Set default paths
		m_elogindPath = ".";
		m_outputPath  = "patches";
	}

	MigrateTree::~MigrateTree() {
		// Restore upstream if needed
		restoreUpstream();
	}

	bool MigrateTree::run() {
		LOG_DEBUG( "Starting migration process" );

		// Initialize source files
		if ( !initializeSourceFiles() ) {
			LOG_ERROR( "Failed to initialize source files" );
			return false;
		}

		// Prepare environment
		if ( !prepareEnvironment() ) {
			LOG_ERROR( "Failed to prepare environment" );
			return false;
		}

		// Discover commits
		if ( !discoverCommits() ) {
			LOG_ERROR( "Failed to discover commits" );
			return false;
		}

		// Generate patches
		if ( !generatePatches() ) {
			LOG_ERROR( "Failed to generate patches" );
			return false;
		}

		// Apply patches
		if ( !applyPatches() ) {
			LOG_ERROR( "Failed to apply patches" );
			return false;
		}

		// Update mutual commits
		if ( !updateMutualCommits() ) {
			LOG_WARNING( "Failed to update mutual commits" );
			// Continue anyway - this is not critical
		}

		LOG_DEBUG( "Migration process completed successfully" );
		return true;
	}

	bool MigrateTree::initializeSourceFiles() {
		LOG_DEBUG( "Initializing source files" );

		// Scan directories for source files (similar to check_tree)
		static std::vector< std::string > const dirs      = { "doc", "docs", "factory", "m4", "man", "po", "shell-completion", "src", "tools" };

		static std::vector< std::string > const rootFiles = {
			".gitignore", ".mailmap", "configure", "meson.build", "meson.version", "meson_options.txt", "TODO"
		};

		for ( auto const& dir : dirs ) {
			std::string dirPath = m_elogindPath + "/" + dir;
			if ( utils::isDirectory( dirPath ) ) {
				auto files = utils::findFiles( dirPath, { "*" } );
				for ( auto const& file : files ) {
					// Skip .pwx files and man/rules
					if ( utils::endsWith( file, ".pwx" ) || file.find( "man/rules/" ) != std::string::npos ) {
						continue;
					}

					// Make relative to source
					std::string relPath = utils::getRelativePath( file, m_elogindPath );
					m_sourceFiles.push_back( relPath );
				}
			}
		}

		// Add root files
		for ( auto const& rootFile : rootFiles ) {
			std::string fullPath = m_elogindPath + "/" + rootFile;
			if ( utils::fileExists( fullPath ) ) {
				m_sourceFiles.push_back( rootFile );
			}
		}

		// Remove duplicates and sort
		std::sort( m_sourceFiles.begin(), m_sourceFiles.end() );
		m_sourceFiles.erase( std::unique( m_sourceFiles.begin(), m_sourceFiles.end() ), m_sourceFiles.end() );

		LOG_DEBUG( "Initialized %zu source files", m_sourceFiles.size() );
		return !m_sourceFiles.empty();
	}

	bool MigrateTree::prepareEnvironment() {
		LOG_DEBUG( "Preparing environment" );

		// Create output directory
		if ( !utils::createDirectory( m_outputPath ) ) {
			LOG_ERROR( "Failed to create output directory: %s", m_outputPath.c_str() );
			return false;
		}

		// Cleanup temporary files
		if ( !cleanupTempFiles() ) {
			LOG_WARNING( "Failed to cleanup temporary files" );
		}

		return true;
	}

	bool MigrateTree::cleanupTempFiles() {
		LOG_DEBUG( "Cleaning up temporary files" );

		static std::vector< std::string > const tempPatterns = { "build*", "*.orig", "*.bak", "*.rej", "*~", "*.gc??" };

		// Cleanup in current directory
		utils::cleanupTempFiles( ".", tempPatterns );

		// Cleanup in output directory
		utils::cleanupTempFiles( m_outputPath, tempPatterns );

		return true;
	}

	bool MigrateTree::discoverCommits() {
		LOG_DEBUG( "Discovering relevant commits" );

		if ( m_upstreamPath.empty() || m_refId.empty() ) {
			LOG_ERROR( "Missing upstream path or target reference" );
			return false;
		}

		// Set up commit discovery
		m_commitDiscovery->setUpstreamPath( m_upstreamPath );
		m_commitDiscovery->setTargetRef( m_refId );
		m_commitDiscovery->setMutualCommit( m_mutualCommit );
		m_commitDiscovery->setSourceFiles( m_sourceFiles );

		// Discover commits
		if ( !m_commitDiscovery->discoverCommits() ) {
			LOG_ERROR( "Failed to discover commits" );
			return false;
		}

		LOG_DEBUG( "Discovered %zu relevant commits", m_commitDiscovery->commits().size() );
		return true;
	}

	bool MigrateTree::generatePatches() {
		LOG_DEBUG( "Generating patches" );

		if ( m_upstreamPath.empty() || m_outputPath.empty() ) {
			LOG_ERROR( "Missing upstream path or output path" );
			return false;
		}

		// Set up patch generator
		m_patchGenerator->setUpstreamPath( m_upstreamPath );
		m_patchGenerator->setOutputPath( m_outputPath );
		m_patchGenerator->setStartCommit( m_mutualCommit );
		m_patchGenerator->setTargetCommit( m_refId );

		// Generate patches for each commit
		auto const& commits = m_commitDiscovery->commits();
		LOG_DEBUG( "Generating patches for %zu commits", commits.size() );

		for ( size_t i = 0; i < commits.size(); ++i ) {
			auto const& commit = commits[i];

			LOG_STATUS( "Generating patch %zu/%zu for commit %s", i + 1, commits.size(), commit.c_str() );

			auto patchFiles = m_patchGenerator->generateCommitPatches( commit, i + 1 );

			// Add to generated patches list
			m_generatedPatches.insert( m_generatedPatches.end(), patchFiles.begin(), patchFiles.end() );

			LOG_DEBUG( "Generated %zu patches for commit %s", patchFiles.size(), commit.c_str() );
		}

		LOG_DEBUG( "Generated %zu total patch files", m_generatedPatches.size() );
		return true;
	}

	bool MigrateTree::applyPatches() {
		LOG_DEBUG( "Applying patches" );

		if ( m_generatedPatches.empty() ) {
			LOG_WARNING( "No patches to apply" );
			return true;
		}

		// Set up patch applier
		m_patchApplier->setElogindPath( m_elogindPath );
		m_patchApplier->setUpstreamPath( m_upstreamPath );

		// Apply patches
		if ( !m_patchApplier->applyPatches( m_generatedPatches, false ) ) {
			LOG_ERROR( "Failed to apply patches" );
			return false;
		}

		m_appliedPatches = m_patchApplier->appliedPatches();
		LOG_DEBUG( "Applied %zu patches successfully", m_appliedPatches.size() );
		return true;
	}

	bool MigrateTree::updateMutualCommits() {
		LOG_DEBUG( "Updating mutual commit tracking" );

		// Set up commit file manager
		m_commitFile->setFilePath( "last_mutual_commits.csv" );

		// Read existing commits
		if ( !m_commitFile->readMutualCommits() ) {
			LOG_WARNING( "Failed to read existing mutual commits" );
		}

		// Update tracking
		// In a real implementation, this would update the CSV with:
		// - New mutual commit (from last applied patch)
		// - New src commit (from upstream)
		// - New tgt commit (from elogind)

		LOG_DEBUG( "Updating mutual commit tracking" );

		// Write back the updated commits
		if ( !m_commitFile->writeMutualCommits() ) {
			LOG_WARNING( "Failed to write updated mutual commits" );
		}

		return true;
	}

	bool MigrateTree::checkoutUpstream() {
		LOG_DEBUG( "Checking out upstream repository" );

		if ( m_upstreamPath.empty() || m_refId.empty() ) {
			LOG_ERROR( "Missing upstream path or target reference" );
			return false;
		}

		GitWrapper git( m_upstreamPath );
		if ( !git.isValid() ) {
			LOG_ERROR( "Invalid upstream repository" );
			return false;
		}

		// Save current commit
		m_previousRefId = git.getHeadCommit();

		// Checkout target
		std::string targetCommit = git.getShortHash( m_refId );
		if ( targetCommit.empty() ) {
			LOG_ERROR( "Failed to resolve target reference: %s", m_refId.c_str() );
			return false;
		}

		// Check if already at target
		std::string currentCommit = git.getHeadCommit();
		if ( currentCommit == targetCommit ) {
			LOG_DEBUG( "Already at target commit %s", targetCommit.c_str() );
			return true;
		}

		// Checkout target
		LOG_STATUS( "Checking out %s in upstream", targetCommit.c_str() );
		return git.checkout( m_refId );
	}

	bool MigrateTree::restoreUpstream() {
		LOG_DEBUG( "Restoring upstream to original state" );

		if ( m_upstreamPath.empty() || m_previousRefId.empty() ) {
			return true; // Nothing to restore
		}

		GitWrapper git( m_upstreamPath );
		if ( !git.isValid() ) {
			return false;
		}

		if ( git.getHeadCommit() != m_previousRefId ) {
			LOG_STATUS( "Restoring upstream to %s", m_previousRefId.c_str() );
			return git.checkout( m_previousRefId );
		}

		return true;
	}

} // namespace migrate
} // namespace elomig
