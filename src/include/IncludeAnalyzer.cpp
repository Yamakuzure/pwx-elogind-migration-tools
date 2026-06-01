/**
 * @file IncludeAnalyzer.cpp
 * @brief Implementation of include directive analysis
 */

#include "IncludeAnalyzer.h"

#include "data/Hunk.h"
#include "utils/StringUtils.h"

#include <regex>

namespace elomig {
namespace include {

	IncludeAnalyzer::IncludeAnalyzer() {
		// Elongind-specific include patterns - handled inline as static
	}

	bool IncludeAnalyzer::analyzeHunk( std::shared_ptr< Hunk > hunk ) {
		if ( !hunk ) {
			return false;
		}

		m_includeMap.clear();

		bool foundIncludes = false;

		for ( size_t i = 0; i < hunk->lineCount(); ++i ) {
			auto const& line = hunk->lineAt( i );

			// Only examine ADDITION and REMOVAL lines
			if ( line.type != LineType::ADDITION && line.type != LineType::REMOVAL ) {
				continue;
			}

			if ( isIncludeDirective( line.content ) ) {
				IncludeInfo info = extractIncludeInfo( line, i );
				if ( !info.fileName.empty() ) {
					m_includeMap[i] = info;
					foundIncludes   = true;
				}
			}
		}

		return foundIncludes;
	}

	IncludeInfo IncludeAnalyzer::getIncludeInfo( int lineIndex ) const {
		auto it = m_includeMap.find( lineIndex );
		if ( it != m_includeMap.end() ) {
			return it->second;
		}
		return IncludeInfo{}; // Empty info
	}

	bool IncludeAnalyzer::isIncludeDirective( std::string const& line ) {
		std::string trimmed = utils::trim( line );

		// Check for #include directives (both with and without whitespace)
		return ( utils::startsWith( trimmed, "#include" ) && ( trimmed.find( "<" ) != std::string::npos || trimmed.find( "\"" ) != std::string::npos ) );
	}

	std::string IncludeAnalyzer::extractIncludeFile( std::string const& line ) {
		std::string trimmed = utils::trim( line );

		// Match #include <filename> or #include "filename"
		static std::regex const includeRegex( R"(#include\s*(["<])([^">]+)[">])" );
		std::smatch             match;

		if ( std::regex_search( trimmed, match, includeRegex ) ) {
			return match[2].str();
		}

		return "";
	}

	std::string IncludeAnalyzer::getIncludeType( std::string const& line ) {
		std::string trimmed = utils::trim( line );

		// Check if it's system include (<file>) or local include ("file")
		if ( utils::startsWith( trimmed, "#include <" ) ) {
			return "system";
		} else if ( utils::startsWith( trimmed, "#include \"" ) ) {
			return "local";
		}

		return "unknown";
	}

	bool IncludeAnalyzer::isElogindInclude( std::string const& fileName ) {
		std::string lowerFile = utils::toLower( fileName );

		// Elongind-specific include patterns
		static std::vector< std::string > const elogindIncludes = {
			"elogind",    "libelogind", "sd-login", "sd-journal", "sd-daemon", "sd-event", "sd-netlink",
			"sd-resolve", "sd-bus",     "sd-path",  "sd-device",  "sd-hwdb",   "sd-id128", "sd-strv"
		};

		for ( auto const& pattern : elogindIncludes ) {
			if ( lowerFile.find( utils::toLower( pattern ) ) != std::string::npos ) {
				return true;
			}
		}

		// Check for specific elogind header files
		if ( fileName.find( "elogind" ) != std::string::npos || fileName.find( "libelogind" ) != std::string::npos ) {
			return true;
		}

		// Check for systemd library headers that should not be changed
		if ( fileName.find( "sd-" ) == 0 ) {
			return true;
		}

		return false;
	}

	IncludeInfo IncludeAnalyzer::extractIncludeInfo( HunkLine const& line, int /*lineIndex*/ ) {
		IncludeInfo info;

		info.fileName  = extractIncludeFile( line.content );
		info.directive = line.original;
		info.type      = getIncludeType( line.content );
		info.isAdded   = ( line.type == LineType::ADDITION );
		info.isRemoved = ( line.type == LineType::REMOVAL );
		info.isElogind = isElogindInclude( info.fileName );

		// Mark as eligible for protection if it's a system include or elogind-specific
		info.isEligible = ( info.type == "system" || info.isElogind );

		return info;
	}

} // namespace include
} // namespace elomig
