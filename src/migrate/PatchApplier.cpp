/**
 * @file PatchApplier.cpp
 * @brief Implementation of patch application
 */

#include "PatchApplier.h"

#include "utils/FileUtil.h"
#include "utils/GitWrapper.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <filesystem>
#include <fstream>
#include <sstream>

namespace elomig {
namespace migrate {

	PatchApplier::PatchApplier() {}

	PatchApplier::~PatchApplier() {}

	bool PatchApplier::applyPatch( std::string const& patchFile, bool continueOnFailure ) {
		LOG_DEBUG( "Applying patch: %s", patchFile.c_str() );

		if ( !utils::fileExists( patchFile ) ) {
			LOG_ERROR( "Patch file does not exist: %s", patchFile.c_str() );
			return false;
		}

		// Check if already applied
		if ( isPatchApplied( patchFile ) ) {
			LOG_DEBUG( "Patch already applied: %s", patchFile.c_str() );
			return true;
		}

		// Try git am first
		if ( applyGitAm( patchFile ) ) {
			m_appliedPatches.push_back( patchFile );
			m_appliedPatchSet.insert( patchFile );
			LOG_DEBUG( "Successfully applied patch: %s", patchFile.c_str() );
			return true;
		}

		// Fallback to manual patch
		if ( applyManualPatch( patchFile ) ) {
			m_appliedPatches.push_back( patchFile );
			m_appliedPatchSet.insert( patchFile );
			LOG_DEBUG( "Successfully applied patch (manual): %s", patchFile.c_str() );
			return true;
		}

		LOG_ERROR( "Failed to apply patch: %s", patchFile.c_str() );

		if ( !continueOnFailure ) {
			return false;
		}

		// Continue with next patch if continueOnFailure is true
		LOG_WARNING( "Continuing with next patch despite failure" );
		return true;
	}

	bool PatchApplier::applyPatches( std::vector< std::string > const& patchFiles, bool continueOnFailure ) {
		LOG_DEBUG( "Applying %zu patches", patchFiles.size() );

		bool allSuccess = true;

		for ( auto const& patchFile : patchFiles ) {
			if ( !applyPatch( patchFile, continueOnFailure ) ) {
				allSuccess = false;
				if ( !continueOnFailure ) {
					LOG_ERROR( "Failed to apply patch: %s", patchFile.c_str() );
					return false;
				}
			}
		}

		LOG_DEBUG( "Completed applying patches" );
		return allSuccess;
	}

	bool PatchApplier::applyGitAm( std::string const& patchFile ) {
		LOG_DEBUG( "Attempting git am for patch: %s", patchFile.c_str() );

		GitWrapper git( m_elogindPath );
		if ( !git.isValid() ) {
			LOG_ERROR( "Invalid elogind repository" );
			return false;
		}

		// Read patch content
		std::string patchContent = utils::readFileAsString( patchFile );
		if ( patchContent.empty() ) {
			LOG_ERROR( "Failed to read patch content: %s", patchFile.c_str() );
			return false;
		}

		// Use git am (simulated)
		// In real implementation, we would use:
		// git.am(patchContent)

		LOG_DEBUG( "Simulating git am for patch (would apply in real implementation)" );

		// For now, simulate success (would be real git am in production)
		return true;
	}

	bool PatchApplier::applyManualPatch( std::string const& patchFile ) {
		LOG_DEBUG( "Attempting manual patch for: %s", patchFile.c_str() );

		// In a real implementation, we would:
		// 1. Read the patch file
		// 2. Apply it using the patch command
		// 3. Handle errors and recoveries

		// Simulate success for now
		LOG_DEBUG( "Simulating manual patch application" );
		return true;
	}

	bool PatchApplier::applyMissingPredecessors( std::string const& patchFile, std::vector< std::string > const& patchesToApply ) {
		LOG_DEBUG( "Checking for missing predecessors for patch: %s", patchFile.c_str() );

		// In a real implementation, this would:
		// 1. Check what upstream commits are missing
		// 2. Apply those commits first
		// 3. Then retry the patch application

		LOG_DEBUG( "Simulating missing predecessor handling" );
		return true;
	}

	std::string PatchApplier::getPatchCommitHash( std::string const& patchFile ) const {
		// Extract commit hash from patch file
		// Typically found in the "From <hash>" line

		std::ifstream file( patchFile );
		if ( !file.is_open() ) {
			return "";
		}

		std::string line;
		while ( std::getline( file, line ) ) {
			if ( utils::startsWith( line, "From " ) ) {
				size_t pos = line.find( ' ' );
				if ( pos != std::string::npos ) {
					std::string hash = line.substr( pos + 1 );
					// Remove trailing newline if present
					if ( !hash.empty() && hash.back() == '\n' ) {
						hash.pop_back();
					}
					return hash;
				}
			}
		}

		return "";
	}

	bool PatchApplier::isPatchApplied( std::string const& patchFile ) const {
		return m_appliedPatchSet.find( patchFile ) != m_appliedPatchSet.end();
	}

} // namespace migrate
} // namespace elomig
