/**
 * @file StringUtils.h
 * @brief String manipulation utilities for elomig
 *
 * Provides common string operations needed throughout the codebase.
 */

#ifndef ELOMIG_STRING_UTILS_H
#define ELOMIG_STRING_UTILS_H

#include <sstream>
#include <string>
#include <vector>

namespace elomig {
namespace utils {

	/**
	 * @brief Trim whitespace from the left of a string
	 * @param s String to trim
	 * @return Trimmed string
	 */
	std::string ltrim( std::string const& s );

	/**
	 * @brief Trim whitespace from the right of a string
	 * @param s String to trim
	 * @return Trimmed string
	 */
	std::string rtrim( std::string const& s );

	/**
	 * @brief Trim whitespace from both ends of a string
	 * @param s String to trim
	 * @return Trimmed string
	 */
	std::string trim( std::string const& s );

	/**
	 * @brief Split a string by delimiter
	 * @param s String to split
	 * @param delimiter Delimiter character
	 * @return Vector of substrings
	 */
	std::vector< std::string > split( std::string const& s, char delimiter );

	/**
	 * @brief Split a string by string delimiter
	 * @param s String to split
	 * @param delimiter Delimiter string
	 * @return Vector of substrings
	 */
	std::vector< std::string > split( std::string const& s, std::string const& delimiter );

	/**
	 * @brief Join strings with delimiter
	 * @param elements Vector of strings to join
	 * @param delimiter Delimiter string
	 * @return Joined string
	 */
	std::string join( std::vector< std::string > const& elements, std::string const& delimiter );

	/**
	 * @brief Replace all occurrences of a substring
	 * @param str String to modify
	 * @param from Substring to find
	 * @param to Substring to replace with
	 * @return Modified string
	 */
	std::string replaceAll( std::string str, std::string const& from, std::string const& to );

	/**
	 * @brief Check if string starts with prefix
	 * @param str String to check
	 * @param prefix Prefix to look for
	 * @return True if string starts with prefix
	 */
	bool startsWith( std::string const& str, std::string const& prefix );

	/**
	 * @brief Check if string ends with suffix
	 * @param str String to check
	 * @param suffix Suffix to look for
	 * @return True if string ends with suffix
	 */
	bool endsWith( std::string const& str, std::string const& suffix );

	/**
	 * @brief Convert string to lowercase
	 * @param str String to convert
	 * @return Lowercase string
	 */
	std::string toLower( std::string const& str );

	/**
	 * @brief Convert string to uppercase
	 * @param str String to convert
	 * @return Uppercase string
	 */
	std::string toUpper( std::string const& str );

	/**
	 * @brief Check if string is empty or whitespace only
	 * @param str String to check
	 * @return True if string is empty or whitespace
	 */
	bool isBlank( std::string const& str );

	/**
	 * @brief Format a string with printf-style formatting
	 * @param format Format string
	 * @param ... Format arguments
	 * @return Formatted string
	 */
	std::string format( char const* format, ... ) __attribute__(( format( printf, 1, 2 ) ));

	/**
	 * @brief Pad a string to a minimum width
	 * @param str String to pad
	 * @param width Minimum width
	 * @param padChar Character to use for padding
	 * @param left If true, pad on left; otherwise pad on right
	 * @return Padded string
	 */
	std::string pad( std::string const& str, size_t width, char padChar = ' ', bool left = true );

	/**
	 * @brief Convert integer to string with optional padding
	 * @param value Integer value
	 * @param width Minimum width (0 for no padding)
	 * @param padChar Padding character
	 * @return String representation
	 */
	std::string toString( int value, size_t width = 0, char padChar = '0' );

} // namespace utils
} // namespace elomig

#endif // ELOMIG_STRING_UTILS_H
