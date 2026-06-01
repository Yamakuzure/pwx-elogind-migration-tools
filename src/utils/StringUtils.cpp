/**
 * @file StringUtils.cpp
 * @brief Implementation of string utility functions
 */

#include "StringUtils.h"

#include <algorithm>
#include <cstdarg>
#include <cstdio>

namespace elomig {
namespace utils {

	std::string ltrim( std::string const& s ) {
		size_t start = s.find_first_not_of( " \t\n\r\f\v" );
		return ( start == std::string::npos ) ? "" : s.substr( start );
	}

	std::string rtrim( std::string const& s ) {
		size_t end = s.find_last_not_of( " \t\n\r\f\v" );
		return ( end == std::string::npos ) ? "" : s.substr( 0, end + 1 );
	}

	std::string trim( std::string const& s ) {
		return rtrim( ltrim( s ) );
	}

	std::vector< std::string > split( std::string const& s, char delimiter ) {
		std::vector< std::string > tokens;
		std::string                token;
		std::istringstream         tokenStream( s );

		while ( std::getline( tokenStream, token, delimiter ) ) {
			tokens.push_back( token );
		}

		return tokens;
	}

	std::vector< std::string > split( std::string const& s, std::string const& delimiter ) {
		std::vector< std::string > tokens;
		size_t                     start = 0;
		size_t                     end   = s.find( delimiter );

		while ( end != std::string::npos ) {
			tokens.push_back( s.substr( start, end - start ) );
			start = end + delimiter.length();
			end   = s.find( delimiter, start );
		}

		tokens.push_back( s.substr( start ) );
		return tokens;
	}

	std::string join( std::vector< std::string > const& elements, std::string const& delimiter ) {
		std::ostringstream oss;

		for ( size_t i = 0; i < elements.size(); ++i ) {
			if ( i > 0 ) {
				oss << delimiter;
			}
			oss << elements[i];
		}

		return oss.str();
	}

	std::string replaceAll( std::string str, std::string const& from, std::string const& to ) {
		if ( from.empty() ) {
			return str;
		}

		size_t start_pos = 0;
		while ( ( start_pos = str.find( from, start_pos ) ) != std::string::npos ) {
			str.replace( start_pos, from.length(), to );
			start_pos += to.length();
		}

		return str;
	}

	bool startsWith( std::string const& str, std::string const& prefix ) {
		if ( prefix.size() > str.size() ) {
			return false;
		}
		return str.compare( 0, prefix.size(), prefix ) == 0;
	}

	bool endsWith( std::string const& str, std::string const& suffix ) {
		if ( suffix.size() > str.size() ) {
			return false;
		}
		return str.compare( str.size() - suffix.size(), suffix.size(), suffix ) == 0;
	}

	std::string toLower( std::string const& str ) {
		std::string result = str;
		std::transform( result.begin(), result.end(), result.begin(), ::tolower );
		return result;
	}

	std::string toUpper( std::string const& str ) {
		std::string result = str;
		std::transform( result.begin(), result.end(), result.begin(), ::toupper );
		return result;
	}

	bool isBlank( std::string const& str ) {
		return str.empty() || trim( str ).empty();
	}

	std::string format( char const* format, ... ) {
		va_list args;
		va_start( args, format );

		char buffer[4'096];
		vsnprintf( buffer, sizeof( buffer ), format, args );
		va_end( args );

		return std::string( buffer );
	}

	std::string pad( std::string const& str, size_t width, char padChar, bool left ) {
		if ( str.length() >= width ) {
			return str;
		}

		size_t      padCount = width - str.length();
		std::string padding( padCount, padChar );

		if ( left ) {
			return padding + str;
		} else {
			return str + padding;
		}
	}

	std::string toString( int value, size_t width, char padChar ) {
		std::string str = std::to_string( value );

		if ( width > 0 && str.length() < width ) {
			return pad( str, width, padChar, true );
		}

		return str;
	}

} // namespace utils
} // namespace elomig
