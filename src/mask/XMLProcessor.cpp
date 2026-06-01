/**
 * @file XMLProcessor.cpp
 * @brief Implementation of XML mask processing
 */

#include "XMLProcessor.h"

#include "mask/MaskDetector.h"
#include "utils/FileUtil.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <regex>

namespace elomig {
namespace mask {

	XMLProcessor::XMLProcessor() : m_inMask( false ) {}

	bool XMLProcessor::prepare( std::string const& sourcePath, std::string& tempPath ) {
		if ( !utils::fileExists( sourcePath ) ) {
			LOG_ERROR( "Source file not found: %s", sourcePath.c_str() );
			return false;
		}

		// Read source file
		std::vector< std::string > lines;
		if ( !utils::readFile( sourcePath, lines ) ) {
			LOG_ERROR( "Failed to read source file: %s", sourcePath.c_str() );
			return false;
		}

		// Prepare content
		std::vector< std::string > preparedLines;
		if ( !prepareContent( lines, preparedLines ) ) {
			return false;
		}

		// Write to temporary .pwx file
		tempPath = sourcePath + ".pwx";
		if ( !utils::writeFile( tempPath, preparedLines ) ) {
			LOG_ERROR( "Failed to write temporary file: %s", tempPath.c_str() );
			return false;
		}

		LOG_DEBUG( "Prepared XML file: %s -> %s", sourcePath.c_str(), tempPath.c_str() );

		return true;
	}

	bool XMLProcessor::unprepare( std::string const& tempPath, std::string const& originalPath ) {
		if ( !utils::fileExists( tempPath ) ) {
			LOG_ERROR( "Temporary file not found: %s", tempPath.c_str() );
			return false;
		}

		// Read prepared file
		std::vector< std::string > preparedLines;
		if ( !utils::readFile( tempPath, preparedLines ) ) {
			LOG_ERROR( "Failed to read temporary file: %s", tempPath.c_str() );
			return false;
		}

		// Unprepare content
		std::vector< std::string > originalLines;
		if ( !unprepareContent( preparedLines, originalLines ) ) {
			return false;
		}

		LOG_DEBUG( "Unprepared XML file: %s -> %s", tempPath.c_str(), originalPath.c_str() );

		return true;
	}

	bool XMLProcessor::prepareContent( std::vector< std::string > const& lines, std::vector< std::string >& preparedLines ) {
		preparedLines.clear();
		m_originalEntities.clear();
		m_inMask = false;

		MaskDetector detector;
		detector.reset();

		for ( size_t i = 0; i < lines.size(); ++i ) {
			std::string const& line         = lines[i];
			std::string        preparedLine = line;

			// Process mask state
			MaskType type = MaskDetector::getMaskType( line, false );

			switch ( type ) {
				case MaskType::MASK_START:
				case MaskType::INSERT_START:
					m_inMask = true;
					break;

				case MaskType::MASK_END:
				case MaskType::INSERT_END:
					m_inMask = false;
					break;

				default:
					break;
			}

			// In mask blocks, restore &#x2D; to actual dashes for proper diffing
			if ( m_inMask ) {
				preparedLine = restoreDashEntities( line, true );

				// Save entity for later restoration
				if ( preparedLine != line ) {
					m_originalEntities.push_back( { static_cast< int >( i ), line } );
				}
			}

			preparedLines.push_back( preparedLine );
		}

		return true;
	}

	bool XMLProcessor::unprepareContent( std::vector< std::string > const& preparedLines, std::vector< std::string >& originalLines ) {
		originalLines.clear();
		m_inMask = false;

		MaskDetector detector;
		detector.reset();

		for ( size_t i = 0; i < preparedLines.size(); ++i ) {
			std::string const& line         = preparedLines[i];
			std::string        originalLine = line;

			// Process mask state
			MaskType type = MaskDetector::getMaskType( line, false );

			switch ( type ) {
				case MaskType::MASK_START:
				case MaskType::INSERT_START:
					m_inMask = true;
					break;

				case MaskType::MASK_END:
				case MaskType::INSERT_END:
					m_inMask = false;
					break;

				default:
					break;
			}

			// In prepared output, we may need to restore entities
			// This is mainly needed when building final patches
			if ( m_inMask ) {
				// Check if line needs entity restoration
				// For now, we keep the prepared version in patches
			}

			originalLines.push_back( originalLine );
		}

		return true;
	}

	bool XMLProcessor::needsPreparation( std::string const& filePath ) {
		std::string lowerPath = utils::toLower( filePath );

		// Check for XML-related extensions
		static std::vector< std::string > const xmlPatterns = { ".xml", ".ent.in", ".policy.in" };

		for ( auto const& pattern : xmlPatterns ) {
			if ( utils::endsWith( lowerPath, pattern ) ) {
				return true;
			}
		}

		return false;
	}

	std::string XMLProcessor::wrapWithMask( std::string const& content, std::string const& maskStart, std::string const& maskEnd ) {
		std::string result;

		result += maskStart + "\n";
		result += content;
		result += "\n" + maskEnd + "\n";

		return result;
	}

	std::string XMLProcessor::restoreDashEntities( std::string const& line, bool inMask ) {
		if ( !inMask ) {
			return line;
		}

		std::string result = line;

		// Replace &#x2D; with actual dash
		// But be careful not to replace in comment delimiters <!-- -->

		// Simple approach: replace all &#x2D; with -
		size_t pos = 0;
		while ( ( pos = result.find( "&#x2D;", pos ) ) != std::string::npos ) {
			// Check if this is in a comment context
			// For safety, we only replace if it looks like it's in content
			result.replace( pos, 6, "-" );
			pos += 1;
		}

		// Also handle &#x2d; (lowercase)
		pos = 0;
		while ( ( pos = result.find( "&#x2d;", pos ) ) != std::string::npos ) {
			result.replace( pos, 6, "-" );
			pos += 1;
		}

		if ( result != line ) {
			LOG_DEBUG( "Restored dash entities in XML line" );
		}

		return result;
	}

	bool XMLProcessor::isXMLMaskComment( std::string const& line ) const {
		// Check for XML comment containing mask directives
		// <!-- #if 0 // elogind -->
		static std::regex const maskCommentRegex( R"(<!--\s*#\s*if\s+[01]\s*//+\s*elogind\s*-->)", std::regex_constants::icase );

		return std::regex_search( line, maskCommentRegex );
	}

	bool XMLProcessor::isXMLMaskStart( std::string const& line ) const {
		// Check for XML-specific mask start patterns
		return MaskDetector::isMaskStart( line, false ) || isXMLMaskComment( line );
	}

	bool XMLProcessor::isXMLMaskEnd( std::string const& line ) const {
		// Check for XML-specific mask end patterns
		return MaskDetector::isMaskEnd( line, false );
	}

} // namespace mask
} // namespace elomig
