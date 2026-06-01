/**
 * @file IncludeReconciler.cpp
 * @brief Implementation of include directive reconciliation
 */

#include "IncludeReconciler.h"

#include "IncludeAnalyzer.h"
#include "data/FileDiff.h"
#include "data/Hunk.h"
#include "utils/StringUtils.h"

#include <regex>

namespace elomig {
namespace include {

	IncludeReconciler::IncludeReconciler() {
		// Initialize elogind-specific include patterns
		m_elogindIncludes = {
			"elogind",    "libelogind", "sd-login", "sd-journal", "sd-daemon", "sd-event", "sd-netlink",
			"sd-resolve", "sd-bus",     "sd-path",  "sd-device",  "sd-hwdb",   "sd-id128", "sd-strv"
		};
	}

	bool IncludeReconciler::processHunk( std::shared_ptr< Hunk > hunk, std::shared_ptr< FileDiff > fileDiff ) {
		if ( !hunk || !fileDiff ) {
			return false;
		}

		bool modified = false;

		// Analyze for include directives
		IncludeAnalyzer analyzer;
		if ( analyzer.analyzeHunk( hunk ) ) {
			// Check for conflicts
			if ( checkConflicts( hunk ) ) {
				modified |= resolveConflicts( hunk );
			}

			// Handle include changes
			modified |= handleIncludeChanges( hunk );

			// Protect elogind includes from removal
			modified |= protectElogindIncludes( hunk );
		}

		return modified;
	}

	bool IncludeReconciler::processFile( std::shared_ptr< FileDiff > fileDiff ) {
		if ( !fileDiff ) {
			return false;
		}

		bool modified = false;

		// Process each hunk in file
		for ( auto& hunk : fileDiff->hunks() ) {
			if ( hunk ) {
				modified |= processHunk( hunk, fileDiff );
			}
		}

		return modified;
	}

	bool IncludeReconciler::checkConflicts( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		// Check if we have conflicting include additions/removals
		// This is a simplified check - full implementation would track
		// across multiple hunks

		return false; // Placeholder - implement full conflict detection
	}

	bool IncludeReconciler::resolveConflicts( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		// Resolve include conflicts (placeholder)
		return false;
	}

	bool IncludeReconciler::handleIncludeChanges( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		bool modified = false;

		// Check for unwanted include additions
		modified |= spliceUnwantedIncludes( hunk );

		return modified;
	}

	bool IncludeReconciler::spliceUnwantedIncludes( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		bool modified = false;

		// Iterate through lines looking for include additions that should be spliced
		for ( size_t i = 0; i < hunk->lineCount(); ++i ) {
			auto& line = hunk->lineAt( i );

			// Check if this is an addition with an include
			if ( line.type == LineType::ADDITION && IncludeAnalyzer::isIncludeDirective( line.content ) ) {

				// Extract include file name
				std::string fileName = IncludeAnalyzer::extractIncludeFile( line.content );

				// Check if this should be spliced out
				if ( shouldProtectInclude( fileName ) && !shouldRevertRemoval( fileName, false ) ) {
					// This is a system include that should be protected
					// For now, just mark as done to prevent processing
					line.done = true;
					modified  = true;
				}
			}
		}

		return modified;
	}

	bool IncludeReconciler::protectElogindIncludes( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		bool modified = false;

		// Look for removals of elogind-specific includes
		for ( size_t i = 0; i < hunk->lineCount(); ++i ) {
			auto& line = hunk->lineAt( i );

			// Check if this is a removal with an include
			if ( line.type == LineType::REMOVAL && IncludeAnalyzer::isIncludeDirective( line.content ) ) {

				// Extract include file name
				std::string fileName = IncludeAnalyzer::extractIncludeFile( line.content );

				// If this is an elogind include, revert the removal
				if ( IncludeAnalyzer::isElogindInclude( fileName ) ) {
					// Convert removal to context to preserve it
					line.type     = LineType::CONTEXT;
					line.original = ' ' + line.content;
					line.done     = true;
					modified      = true;
				}
			}
		}

		return modified;
	}

	bool IncludeReconciler::shouldProtectInclude( std::string const& fileName ) {
		// Check if this include should be protected from removal
		if ( fileName.empty() ) {
			return false;
		}

		// System includes or specific elogind includes typically should be protected
		return IncludeAnalyzer::isElogindInclude( fileName );
	}

	bool IncludeReconciler::shouldRevertRemoval( std::string const& fileName, bool isRemoved ) {
		if ( fileName.empty() || !isRemoved ) {
			return false;
		}

		// Revert removals of elogind-specific includes
		return IncludeAnalyzer::isElogindInclude( fileName );
	}

	std::vector< std::string > const& IncludeReconciler::getElogindIncludePatterns() {
		static std::vector< std::string > const patterns = {
			"elogind",    "libelogind", "sd-login", "sd-journal", "sd-daemon", "sd-event", "sd-netlink",
			"sd-resolve", "sd-bus",     "sd-path",  "sd-device",  "sd-hwdb",   "sd-id128", "sd-strv"
		};
		return patterns;
	}

} // namespace include
} // namespace elomig
