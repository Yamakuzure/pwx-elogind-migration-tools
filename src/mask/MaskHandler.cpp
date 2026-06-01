/**
 * @file MaskHandler.cpp
 * @brief Implementation of mask block handling
 */

#include "MaskHandler.h"

#include "data/FileDiff.h"
#include "data/Hunk.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

namespace elomig {
namespace mask {

	MaskHandler::MaskHandler() {}

	bool MaskHandler::processHunk( std::shared_ptr< Hunk > hunk, std::shared_ptr< FileDiff > fileDiff ) {
		if ( !hunk || !fileDiff ) {
			return false;
		}

		reset();
		m_maskLines.clear();
		m_inMask.clear();
		m_maskLevels.clear();

		bool isShell  = fileDiff->isShell();
		bool modified = false;

		// First pass: detect all mask lines and build state
		auto const& lines = hunk->lines();
		for ( size_t i = 0; i < lines.size(); ++i ) {
			std::string fullLine = lines[i].original;
			MaskLine    maskLine = m_detector.processLine( fullLine, i, isShell );

			m_maskLines.push_back( maskLine );
			m_inMask.push_back( m_detector.isInMask() || m_detector.isInInsert() );
			m_maskLevels.push_back( m_detector.getNestLevel() );

			if ( maskLine.type != MaskType::NONE ) {
				LOG_DEBUG( "Found mask directive at line %zu: type=%d", i, static_cast< int >( maskLine.type ) );
			}
		}

		// Second pass: apply mask handling rules
		modified |= sanitizeMasks( hunk );
		modified |= handleMaskRemovals( hunk );
		modified |= handleMaskAdditions( hunk );

		// Update hunk mask flags
		if ( !m_maskLines.empty() ) {
			// Check if hunk starts in mask
			if ( m_inMask[0] ) {
				hunk->setMaskedStart( true );
				LOG_DEBUG( "Hunk %d starts in mask block", hunk->index() );
			}

			// Check if hunk ends in mask
			if ( m_inMask.back() ) {
				hunk->setMaskedEnd( true );
				LOG_DEBUG( "Hunk %d ends in mask block", hunk->index() );
			}
		}

		return modified;
	}

	bool MaskHandler::checkMaskStructure( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		reset();
		int maskCount  = 0;
		int elseCount  = 0;
		int endifCount = 0;

		for ( auto const& line : hunk->lines() ) {
			MaskType type = m_detector.checkLine( line.original, false );

			switch ( type ) {
				case MaskType::MASK_START:
				case MaskType::INSERT_START:
					maskCount++;
					break;
				case MaskType::MASK_ELSE:
					elseCount++;
					break;
				case MaskType::MASK_END:
				case MaskType::INSERT_END:
					endifCount++;
					break;
				default:
					break;
			}
		}

		// Basic structure check: should have matching if/endif
		bool valid = ( maskCount == endifCount );

		if ( !valid ) {
			LOG_WARNING( "Mask structure mismatch in hunk %d: %d starts, %d ends", hunk->index(), maskCount, endifCount );
		}

		return valid;
	}

	int MaskHandler::sanitizeMasks( std::shared_ptr< Hunk > hunk ) {
		int fixes = 0;

		if ( !hunk ) {
			return 0;
		}

		// Look for common mask issues and fix them

		auto& lines = hunk->lines();
		for ( size_t i = 0; i < lines.size(); ++i ) {
			// Check for removals inside mask blocks that should be spaces
			if ( lines[i].type == LineType::REMOVAL && i < m_inMask.size() && m_inMask[i] ) {
				// Convert removal to space (keep the line)
				lines[i].type     = LineType::CONTEXT;
				lines[i].original = ' ' + lines[i].content;
				lines[i].done     = true;
				fixes++;
				LOG_DEBUG( "Sanitized removal inside mask at line %zu", i );
			}
		}

		return fixes;
	}

	bool MaskHandler::handleMaskRemovals( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		bool  modified = false;
		auto& lines    = hunk->lines();

		// Track undone removals for potential matching with additions
		std::vector< size_t > undoneRemovals;

		for ( size_t i = 0; i < lines.size(); ++i ) {
			if ( lines[i].type != LineType::REMOVAL ) {
				continue;
			}

			// Check if removal is inside a mask block
			if ( i < m_inMask.size() && m_inMask[i] ) {
				// Don't remove code that's protected by elogind mask
				// Convert removal to space (keep the line as context)
				lines[i].type     = LineType::CONTEXT;
				lines[i].original = ' ' + lines[i].content;
				lines[i].done     = true;
				undoneRemovals.push_back( i );
				modified = true;

				LOG_DEBUG( "Protected removal in mask at line %zu: %s", i, lines[i].content.c_str() );
			}
		}

		return modified;
	}

	bool MaskHandler::handleMaskAdditions( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		bool  modified = false;
		auto& lines    = hunk->lines();

		for ( size_t i = 0; i < lines.size(); ++i ) {
			if ( lines[i].type != LineType::ADDITION ) {
				continue;
			}

			// Check if this addition should be moved into a mask block
			// Look backwards for a mask else or end
			for ( int j = static_cast< int >( i ) - 1; j >= 0; --j ) {
				if ( j >= static_cast< int >( m_maskLines.size() ) ) {
					continue;
				}

				MaskType type = m_maskLines[j].type;

				// If we hit a mask else, consider moving addition before it
				if ( type == MaskType::MASK_ELSE ) {
					// Check if addition matches a removal that was undone
					// This is a simplified check - full implementation would
					// compare with undoneRemovals from handleMaskRemovals
					break;
				}

				// If we hit a non-mask line, stop looking
				if ( type == MaskType::NONE ) {
					break;
				}
			}
		}

		return modified;
	}

	bool MaskHandler::convertEmptyMask( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		bool  modified = false;
		auto& lines    = hunk->lines();

		// Find mask blocks and check if they're empty (no real changes)
		size_t i = 0;
		while ( i < lines.size() ) {
			if ( m_maskLines[i].type == MaskType::MASK_START ) {
				int startIdx = static_cast< int >( i );
				int endIdx   = findMatchingEndif( i );

				if ( endIdx > 0 ) {
					// Check if mask block has any real changes
					bool hasChanges = false;
					for ( int j = startIdx + 1; j < endIdx && !hasChanges; ++j ) {
						if ( lines[j].type != LineType::CONTEXT && !lines[j].done ) {
							hasChanges = true;
						}
					}

					if ( !hasChanges ) {
						// Convert empty mask to comment
						LOG_DEBUG( "Converting empty mask at lines %d-%d", startIdx, endIdx );

						// Mark the mask directives as done (neutral)
						lines[startIdx].type = LineType::CONTEXT;
						lines[startIdx].done = true;

						if ( m_maskLines[startIdx + 1].type == MaskType::MASK_ELSE ) {
							lines[startIdx + 1].type = LineType::CONTEXT;
							lines[startIdx + 1].done = true;
						}

						lines[endIdx].type = LineType::CONTEXT;
						lines[endIdx].done = true;

						modified           = true;
					}

					i = endIdx + 1;
					continue;
				}
			}
			i++;
		}

		return modified;
	}

	bool MaskHandler::isLineInMask( size_t lineIndex ) const {
		if ( lineIndex >= m_inMask.size() ) {
			return false;
		}
		return m_inMask[lineIndex];
	}

	int MaskHandler::getMaskLevelAt( size_t lineIndex ) const {
		if ( lineIndex >= m_maskLevels.size() ) {
			return 0;
		}
		return m_maskLevels[lineIndex];
	}

	int MaskHandler::findMatchingEndif( size_t startIndex ) const {
		if ( startIndex >= m_maskLines.size() ) {
			return -1;
		}

		MaskType startType = m_maskLines[startIndex].type;
		if ( startType != MaskType::MASK_START && startType != MaskType::INSERT_START ) {
			return -1;
		}

		int level = 1;
		for ( size_t i = startIndex + 1; i < m_maskLines.size(); ++i ) {
			MaskType type = m_maskLines[i].type;

			if ( type == MaskType::MASK_START || type == MaskType::INSERT_START ) {
				level++;
			} else if ( type == MaskType::MASK_END || type == MaskType::INSERT_END ) {
				level--;
				if ( level == 0 ) {
					return static_cast< int >( i );
				}
			}
		}

		return -1; // No matching endif found
	}

} // namespace mask
} // namespace elomig
