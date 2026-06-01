/**
 * @file FileUtil.h
 * @brief File system utilities for elomig
 *
 * Provides file and directory operations needed for source tree processing.
 */

#ifndef ELOMIG_FILE_UTIL_H
#define ELOMIG_FILE_UTIL_H

#include <filesystem>
#include <set>
#include <string>
#include <vector>

namespace elomig {
namespace utils {

	namespace fs = std::filesystem;

	/**
	 * @brief Check if a file exists
	 * @param path File path
	 * @return True if file exists
	 */
	bool fileExists( std::string const& path );

	/**
	 * @brief Check if a path is a directory
	 * @param path Directory path
	 * @return True if path is a directory
	 */
	bool isDirectory( std::string const& path );

	/**
	 * @brief Create directory if it doesn't exist
	 * @param path Directory path
	 * @return True if directory exists or was created
	 */
	bool createDirectory( std::string const& path );

	/**
	 * @brief Read entire file contents
	 * @param path File path
	 * @param lines Output vector of lines
	 * @return True if file was read successfully
	 */
	bool readFile( std::string const& path, std::vector< std::string >& lines );

	/**
	 * @brief Read entire file as single string
	 * @param path File path
	 * @return File contents
	 */
	std::string readFileAsString( std::string const& path );

	/**
	 * @brief Write lines to file
	 * @param path File path
	 * @param lines Lines to write
	 * @return True if file was written successfully
	 */
	bool writeFile( std::string const& path, std::vector< std::string > const& lines );

	/**
	 * @brief Write string to file
	 * @param path File path
	 * @param content Content to write
	 * @return True if file was written successfully
	 */
	bool writeFile( std::string const& path, std::string const& content );

	/**
	 * @brief Get absolute path
	 * @param path Relative or absolute path
	 * @return Absolute path
	 */
	std::string getAbsolutePath( std::string const& path );

	/**
	 * @brief Get directory name from path
	 * @param path File path
	 * @return Directory component
	 */
	std::string getDirectoryName( std::string const& path );

	/**
	 * @brief Get base name from path
	 * @param path File path
	 * @return Filename component
	 */
	std::string getBaseName( std::string const& path );

	/**
	 * @brief Get file extension
	 * @param path File path
	 * @return Extension (including dot)
	 */
	std::string getExtension( std::string const& path );

	/**
	 * @brief Get current working directory
	 * @return Current working directory path
	 */
	std::string getCurrentWorkingDirectory();

	/**
	 * @brief Find all files matching patterns in directory tree
	 * @param rootDir Root directory to search
	 * @param patterns File patterns to match (e.g., "*.c", "*.h")
	 * @param excludeDirs Directories to exclude from search
	 * @return Vector of matching file paths
	 */
	std::vector< std::string > findFiles( std::string const& rootDir, std::vector< std::string > const& patterns, std::set< std::string > const& excludeDirs = {} );

	/**
	 * @brief Copy a file
	 * @param source Source file path
	 * @param dest Destination file path
	 * @return True if copy succeeded
	 */
	bool copyFile( std::string const& source, std::string const& dest );

	/**
	 * @brief Delete a file
	 * @param path File path to delete
	 * @return True if file was deleted or doesn't exist
	 */
	bool deleteFile( std::string const& path );

	/**
	 * @brief Get file size
	 * @param path File path
	 * @return File size in bytes, or -1 if error
	 */
	ssize_t getFileSize( std::string const& path );

	/**
	 * @brief Check if path has one of the given extensions
	 * @param path File path
	 * @param extensions Vector of extensions to check (e.g., {".c", ".h"})
	 * @return True if path has matching extension
	 */
	bool hasExtension( std::string const& path, std::vector< std::string > const& extensions );

	/**
	 * @brief Normalize path separators
	 * @param path Path to normalize
	 * @return Normalized path
	 */
	std::string normalizePath( std::string const& path );

	/**
	 * @brief Get relative path from base
	 * @param path Absolute path
	 * @param base Base directory
	 * @return Relative path from base to path
	 */
	std::string getRelativePath( std::string const& path, std::string const& base );

	/**
	 * @brief Clean up temporary files matching patterns
	 * @param directory Directory to clean
	 * @param patterns Patterns to match (e.g., "*.orig", "*.bak")
	 */
	void cleanupTempFiles( std::string const& directory, std::vector< std::string > const& patterns );

} // namespace utils
} // namespace elomig

#endif // ELOMIG_FILE_UTIL_H
