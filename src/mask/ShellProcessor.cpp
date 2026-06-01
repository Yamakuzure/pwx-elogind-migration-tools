/**
 * @file ShellProcessor.cpp
 * @brief Implementation of shell script mask processing
 */

#include "ShellProcessor.h"

#include "mask/MaskDetector.h"
#include "utils/FileUtil.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

namespace elomig {
namespace mask {

	ShellProcessor::ShellProcessor() : m_prepared( false ) {}

	bool ShellProcessor::prepare( std::string const& sourcePath, std::string& tempPath ) {
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

		m_prepared = true;
		LOG_DEBUG( "Prepared shell file: %s -> %s", sourcePath.c_str(), tempPath.c_str() );

		return true;
	}

	bool ShellProcessor::unprepare( std::string const& tempPath, std::string const& originalPath ) {
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

		// Write back to original location (if needed)
		// Usually this is done in the patch building phase
		LOG_DEBUG( "Unprepared shell file: %s -> %s", tempPath.c_str(), originalPath.c_str() );

		m_prepared = false;

		return true;
	}

	bool ShellProcessor::prepareContent( std::vector< std::string > const& lines, std::vector< std::string >& preparedLines ) {
		preparedLines.clear();
		m_originalMasks.clear();

		MaskDetector detector;
		detector.reset();

		for ( size_t i = 0; i < lines.size(); ++i ) {
			std::string const& line         = lines[i];
			std::string        preparedLine = line;

			// Check if this is a mask directive
			MaskType type = MaskDetector::getMaskType( line, true );

			if ( type != MaskType::NONE ) {
				// Save original line
				m_originalMasks.push_back( { static_cast< int >( i ), line } );

				// Comment out the mask directive
				preparedLine = commentMaskLine( line );
				LOG_DEBUG( "Commented mask at line %zu: %s", i, line.c_str() );
			}

			preparedLines.push_back( preparedLine );
		}

		m_prepared = true;
		return true;
	}

	bool ShellProcessor::unprepareContent( std::vector< std::string > const& preparedLines, std::vector< std::string >& originalLines ) {
		originalLines.clear();

		MaskDetector detector;
		detector.reset();

		for ( size_t i = 0; i < preparedLines.size(); ++i ) {
			std::string const& line         = preparedLines[i];
			std::string        originalLine = line;

			// Check if this looks like a commented mask directive
			std::string trimmed = utils::trim( line );

			// Check for commented mask patterns
			if ( utils::startsWith( trimmed, "##" ) || ( utils::startsWith( trimmed, "#" ) && utils::startsWith( trimmed.substr( 1 ), "#" ) ) ) {

				// Remove the extra # that was added
				std::string uncommented = line;
				if ( utils::startsWith( trimmed, "##" ) ) {
					// Remove first #
					size_t pos = line.find( '#' );
					if ( pos != std::string::npos ) {
						uncommented = line.substr( 0, pos ) + line.substr( pos + 1 );
					}
				}

				// Check if it's now a valid mask directive
				MaskType type = MaskDetector::getMaskType( uncommented, false );
				if ( type != MaskType::NONE ) {
					originalLine = uncommented;
					LOG_DEBUG( "Uncommented mask at line %zu", i );
				}
			}

			originalLines.push_back( originalLine );
		}

		m_prepared = false;
		return true;
	}

	bool ShellProcessor::needsPreparation( std::string const& filePath ) {
		// Check if file has shell script patterns
		static std::vector< std::string > const shellPatterns = {
			".sh", ".pl", ".py", ".in", ".m4", ".sym", "meson.build", "meson.options", "Makefile", ".gitignore", ".gperf"
		};

		std::string lowerPath = utils::toLower( filePath );

		for ( auto const& pattern : shellPatterns ) {
			if ( utils::endsWith( lowerPath, pattern ) || lowerPath.find( pattern ) != std::string::npos ) {
				return true;
			}
		}

		return false;
	}

	std::vector< std::string > const& ShellProcessor::getMaskPatterns() {
		static std::vector< std::string > const
			patterns = { R"(#\s*if\s+0\s+//+\s*elogind)", R"(#\s*if\s+1\s+//+\s*elogind)", R"(#\s*else\s+//\s*[01])", R"(#\s*endif\s+//\s*[01])" };
		return patterns;
	}

	std::string ShellProcessor::commentMaskLine( std::string const& line ) {
		// For shell files, we add an extra # to comment out the mask directive
		// Original: #if 0 // elogind
		// Prepared: ##if 0 // elogind  or  # #if 0 // elogind

		std::string trimmed      = utils::ltrim( line );
		std::string leadingSpace = line.substr( 0, line.length() - trimmed.length() );

		// Add # after the leading #
		if ( utils::startsWith( trimmed, "#" ) ) {
			return leadingSpace + "# " + trimmed.substr( 1 );
		}

		return line;
	}

	std::string ShellProcessor::uncommentMaskLine( std::string const& line ) {
		std::string trimmed      = utils::ltrim( line );
		std::string leadingSpace = line.substr( 0, line.length() - trimmed.length() );

		// Remove the extra #
		if ( utils::startsWith( trimmed, "# #" ) ) {
			return leadingSpace + "#" + trimmed.substr( 2 );
		}
		if ( utils::startsWith( trimmed, "##" ) ) {
			return leadingSpace + trimmed.substr( 1 );
		}

		return line;
	}

	bool ShellProcessor::isMaskDirective( std::string const& line ) const {
		return MaskDetector::getMaskType( line, true ) != MaskType::NONE;
	}

} // namespace mask
} // namespace elomig
