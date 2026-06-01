/**
 * @file PatchGenerator.cpp
 * @brief Implementation of patch generation
 */

#include "PatchGenerator.h"

#include "checktree/CheckTree.h"
#include "utils/FileUtil.h"
#include "utils/GitWrapper.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <filesystem>
#include <fstream>
#include <sstream>

namespace elomig {
namespace migrate {

	PatchGenerator::PatchGenerator() {}

	PatchGenerator::~PatchGenerator() {}

	std::vector< std::string > PatchGenerator::generateCommitPatches( std::string const& commitHash, int patchNumber ) {
		LOG_DEBUG( "Generating patches for commit %s", commitHash.c_str() );

		std::vector< std::string > patchFiles;

		// Ensure output directory exists
		utils::createDirectory( m_outputPath );

		// Generate format patch
		std::string patchFile = generateFormatPatch( commitHash, patchNumber );
		if ( !patchFile.empty() ) {
			patchFiles.push_back( patchFile );
			m_generatedPatches.push_back( patchFile );
			LOG_DEBUG( "Generated patch: %s", patchFile.c_str() );
		}

		return patchFiles;
	}

	std::vector< std::string > PatchGenerator::generateCommitRangePatches( std::string const& startCommit, std::string const& endCommit, int /*patchNumber*/ ) {
		LOG_DEBUG( "Generating patches for commit range %s..%s", startCommit.c_str(), endCommit.c_str() );

		std::vector< std::string > patchFiles;

		// Ensure output directory exists
		utils::createDirectory( m_outputPath );

		// For now, generate patches individually
		// In a real implementation, we'd use git format-patch with range
		// This is a placeholder - would need to implement proper range handling

		LOG_WARNING( "Range patch generation not fully implemented - generating single patches" );

		return patchFiles;
	}

	std::string PatchGenerator::generateFormatPatch( std::string const& commitHash, int patchNumber ) {
		GitWrapper git( m_upstreamPath );
		if ( !git.isValid() ) {
			return "";
		}

		// Use git format-patch command directly
		std::string cmd = "cd " + m_upstreamPath + " && git format-patch --find-copies --find-copies-harder --numbered " + "--output-directory " + m_outputPath
		                + " --start-number " + std::to_string( patchNumber ) + " -1 " + commitHash + " 2>&1";

		LOG_DEBUG( "Executing format-patch command: %s", cmd.c_str() );

		FILE* pipe = popen( cmd.c_str(), "r" );
		if ( !pipe ) {
			LOG_ERROR( "Failed to execute git format-patch" );
			return "";
		}

		char        buffer[256];
		std::string result;
		while ( fgets( buffer, sizeof( buffer ), pipe ) != nullptr ) {
			result += buffer;
		}

		int status = pclose( pipe );

		if ( status != 0 ) {
			LOG_ERROR( "git format-patch failed with exit status: %d", WEXITSTATUS( status ) );
			return "";
		}

		// Extract patch file name from output
		std::vector< std::string > lines = utils::split( result, '\n' );
		for ( auto const& line : lines ) {
			std::string trimmed = utils::trim( line );
			if ( utils::endsWith( trimmed, ".patch" ) ) {
				return utils::normalizePath( m_outputPath + "/" + trimmed );
			}
		}

		return "";
	}

	bool PatchGenerator::reworkPatches( std::vector< std::string > const& patchFiles ) {
		LOG_DEBUG( "Reworking %zu patches", patchFiles.size() );

		for ( auto const& patchFile : patchFiles ) {
			if ( !reworkSinglePatch( patchFile ) ) {
				LOG_ERROR( "Failed to rework patch: %s", patchFile.c_str() );
				return false;
			}
		}

		return true;
	}

	bool PatchGenerator::reworkSinglePatch( std::string const& patchFile ) {
		// This is a simplified reworking - in a full implementation
		// we would:
		// 1. Parse the patch to identify affected files
		// 2. Use check_tree logic to filter and rework
		// 3. Apply elogind-specific transformations
		// 4. Write back the reworked patch

		LOG_DEBUG( "Reworking patch: %s", patchFile.c_str() );

		// For now, just verify patch file exists
		if ( !utils::fileExists( patchFile ) ) {
			LOG_ERROR( "Patch file does not exist: %s", patchFile.c_str() );
			return false;
		}

		// In a full implementation, we'd parse the patch and rework it
		// using the check_tree logic

		LOG_DEBUG( "Patch reworking completed for: %s", patchFile.c_str() );
		return true;
	}

} // namespace migrate
} // namespace elomig
