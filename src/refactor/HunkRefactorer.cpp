/**
 * @file HunkRefactorer.cpp
 * @brief Implementation of hunk refactorer
 */

#include "HunkRefactorer.h"

#include "data/FileDiff.h"
#include "data/Hunk.h"
#include "include/IncludeReconciler.h"
#include "mask/MaskHandler.h"
#include "reversion/NameReverter.h"
#include "utils/Logger.h"

namespace elomig {

HunkRefactorer::HunkRefactorer()
	: m_debugMode( false )
	, m_nameReverter( std::make_unique< reversion::NameReverter >() )
	, m_includeReconciler( std::make_unique< include::IncludeReconciler >() ) {}

HunkRefactorer::~HunkRefactorer() {}

void HunkRefactorer::processHunk( std::shared_ptr< Hunk > hunk, std::shared_ptr< FileDiff > fileDiff ) {
	if ( !hunk || !hunk->isUseful() ) {
		return;
	}

	LOG_DEBUG( "Processing hunk %d", hunk->index() );

	// First: Handle mask blocks (most important)
	mask::MaskHandler maskHandler;
	if ( maskHandler.processHunk( hunk, fileDiff ) ) {
		LOG_DEBUG( "Mask handler modified hunk %d", hunk->index() );
	}

	// Second: Handle name reversions
	if ( m_nameReverter ) {
		bool isShell = fileDiff->isShell();
		bool isXML   = fileDiff->isXML();
		if ( m_nameReverter->processHunk( hunk, isShell, isXML ) ) {
			LOG_DEBUG( "Name reverter modified hunk %d", hunk->index() );
		}
	}

	// Third: Handle include directives
	if ( m_includeReconciler ) {
		if ( m_includeReconciler->processHunk( hunk, fileDiff ) ) {
			LOG_DEBUG( "Include reconciler modified hunk %d", hunk->index() );
		}
	}

	// Run all other refactoring passes
	checkMusl( hunk );
	checkDebug( hunk );
	checkUseless( hunk );
	checkEmptyMasks( hunk );
	checkComments( hunk );
	checkFunctions( hunk );
}

void HunkRefactorer::finishHunks( std::shared_ptr< FileDiff > fileDiff ) {
	// Final processing passes
	for ( auto& hunk : fileDiff->hunks() ) {
		if ( !hunk ) {
			continue;
		}

		// Count real changes
		if ( !hunk->hasChanges() ) {
			hunk->setUseful( false );
		}
	}
}

bool HunkRefactorer::checkHunkSanity( std::shared_ptr< Hunk > hunk ) {
	if ( !hunk ) {
		return false;
	}

	// Basic sanity checks
	if ( hunk->lineCount() == 0 ) {
		return false;
	}

	// Check for valid line types
	for ( auto const& line : hunk->lines() ) {
		if ( line.type != LineType::CONTEXT && line.type != LineType::ADDITION && line.type != LineType::REMOVAL ) {
			return false;
		}
	}

	return true;
}

void HunkRefactorer::checkMasks( std::shared_ptr< Hunk > hunk, std::shared_ptr< FileDiff > fileDiff ) {
	// Now handled by MaskHandler
	( void )hunk;
	( void )fileDiff;
}

void HunkRefactorer::checkMusl( std::shared_ptr< Hunk > hunk ) {
	// TODO: Implement __GLIBC__ block handling
	( void )hunk;
}

void HunkRefactorer::checkDebug( std::shared_ptr< Hunk > hunk ) {
	// TODO: Implement debug block handling
	( void )hunk;
}

void HunkRefactorer::checkNameReverts( std::shared_ptr< Hunk > hunk ) {
	// Now handled by NameReverter class
	( void )hunk;
}

void HunkRefactorer::checkUseless( std::shared_ptr< Hunk > hunk ) {
	// TODO: Implement useless change detection
	( void )hunk;
}

void HunkRefactorer::checkEmptyMasks( std::shared_ptr< Hunk > hunk ) {
	// TODO: Implement empty mask detection
	( void )hunk;
}

void HunkRefactorer::checkIncludes( std::shared_ptr< Hunk > hunk ) {
	// Now handled by IncludeReconciler class
	( void )hunk;
}

void HunkRefactorer::checkComments( std::shared_ptr< Hunk > hunk ) {
	// TODO: Implement comment handling
	( void )hunk;
}

void HunkRefactorer::checkFunctions( std::shared_ptr< Hunk > hunk ) {
	// TODO: Implement function call protection
	( void )hunk;
}

} // namespace elomig
