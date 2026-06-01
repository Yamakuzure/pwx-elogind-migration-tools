/**
 * @file MaskDetector.cpp
 * @brief Implementation of mask block detection
 */

#include "MaskDetector.h"

#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <regex>

namespace elomig {
namespace mask {

	MaskDetector::MaskDetector() : m_nestLevel( 0 ), m_inMask( false ), m_inInsert( false ), m_inMaskElse( false ), m_lastMaskLevel( 0 ) {}

	void MaskDetector::reset() {
		m_nestLevel     = 0;
		m_inMask        = false;
		m_inInsert      = false;
		m_inMaskElse    = false;
		m_lastMaskLevel = 0;
	}

	MaskType MaskDetector::checkLine( std::string const& line, bool isShell ) const {
		return getMaskType( line, isShell );
	}

	MaskType MaskDetector::getMaskType( std::string const& line, bool isShell ) {
		std::string trimmed = utils::trim( line );

		// For shell files, remove leading # comment markers
		if ( isShell ) {
			// Check if line starts with # (possibly with spaces)
			std::string checkLine = trimmed;
			if ( utils::startsWith( checkLine, "#" ) ) {
				// Remove the # and trim again
				checkLine = utils::trim( checkLine.substr( 1 ) );

				// Now check if it looks like a preprocessor directive
				if ( utils::startsWith( checkLine, "if " ) || utils::startsWith( checkLine, "if\t" ) || utils::startsWith( checkLine, "else" )
				     || utils::startsWith( checkLine, "endif" ) ) {
					trimmed = checkLine;
				}
			}
		}

		// Check for mask start: #if 0 // elogind or #if 0 /// elogind
		static std::regex const maskStartRegex( R"(^#\s*if\s+0\s+//+\s*elogind)", std::regex_constants::icase );

		// Check for insert start: #if 1 // elogind
		static std::regex const insertStartRegex( R"(^#\s*if\s+1\s+//+\s*elogind)", std::regex_constants::icase );

		// Check for mask/insert else: #else // 0 or #else // 1
		static std::regex const elseRegex( R"(^#\s*else\s+//\s*[01])" );

		// Check for mask end: #endif // 0
		static std::regex const maskEndRegex( R"(^#\s*endif\s+//\s*0)" );

		// Check for insert end: #endif // 1
		static std::regex const insertEndRegex( R"(^#\s*endif\s+//\s*1)" );

		if ( std::regex_search( trimmed, maskStartRegex ) ) {
			return MaskType::MASK_START;
		}

		if ( std::regex_search( trimmed, insertStartRegex ) ) {
			return MaskType::INSERT_START;
		}

		if ( std::regex_search( trimmed, elseRegex ) ) {
			return MaskType::MASK_ELSE;
		}

		if ( std::regex_search( trimmed, maskEndRegex ) ) {
			return MaskType::MASK_END;
		}

		if ( std::regex_search( trimmed, insertEndRegex ) ) {
			return MaskType::INSERT_END;
		}

		return MaskType::NONE;
	}

	bool MaskDetector::isMaskStart( std::string const& line, bool isShell ) {
		return getMaskType( line, isShell ) == MaskType::MASK_START;
	}

	bool MaskDetector::isMaskElse( std::string const& line, bool isShell ) {
		return getMaskType( line, isShell ) == MaskType::MASK_ELSE;
	}

	bool MaskDetector::isMaskEnd( std::string const& line, bool isShell ) {
		return getMaskType( line, isShell ) == MaskType::MASK_END;
	}

	bool MaskDetector::isInsertStart( std::string const& line, bool isShell ) {
		return getMaskType( line, isShell ) == MaskType::INSERT_START;
	}

	bool MaskDetector::isInsertEnd( std::string const& line, bool isShell ) {
		return getMaskType( line, isShell ) == MaskType::INSERT_END;
	}

	MaskLine MaskDetector::processLine( std::string const& line, int lineNumber, bool isShell ) {
		MaskLine result;
		result.lineNumber  = lineNumber;
		result.content     = line;
		result.isCommented = isShell && utils::trim( line )[0] == '#';
		result.nestLevel   = m_nestLevel;

		MaskType type      = checkLine( line, isShell );
		result.type        = type;

		switch ( type ) {
			case MaskType::MASK_START:
				m_nestLevel++;
				m_lastMaskLevel = m_nestLevel;
				m_inMask        = true;
				m_inMaskElse    = false;
				LOG_DEBUG( "Mask START at line %d (level %d)", lineNumber, m_nestLevel );
				break;

			case MaskType::MASK_ELSE:
				m_inMaskElse = true;
				LOG_DEBUG( "Mask ELSE at line %d (level %d)", lineNumber, m_nestLevel );
				break;

			case MaskType::MASK_END:
				if ( m_nestLevel > 0 ) {
					m_nestLevel--;
				}
				if ( m_nestLevel == 0 ) {
					m_inMask     = false;
					m_inMaskElse = false;
				}
				LOG_DEBUG( "Mask END at line %d (level %d)", lineNumber, m_nestLevel );
				break;

			case MaskType::INSERT_START:
				m_nestLevel++;
				m_inInsert   = true;
				m_inMaskElse = false;
				LOG_DEBUG( "Insert START at line %d (level %d)", lineNumber, m_nestLevel );
				break;

			case MaskType::INSERT_END:
				if ( m_nestLevel > 0 ) {
					m_nestLevel--;
				}
				if ( m_nestLevel == 0 ) {
					m_inInsert = false;
				}
				LOG_DEBUG( "Insert END at line %d (level %d)", lineNumber, m_nestLevel );
				break;

			default:
				break;
		}

		return result;
	}

} // namespace mask
} // namespace elomig
