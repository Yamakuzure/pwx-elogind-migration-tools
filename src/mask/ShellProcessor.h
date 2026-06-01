/**
 * @file ShellProcessor.h
 * @brief Process shell scripts for mask block handling
 *
 * Handles preparation and unpreparation of shell scripts,
 * where mask blocks need to be commented out to prevent
 * diff from moving them.
 */

#ifndef ELOMIG_SHELL_PROCESSOR_H
#define ELOMIG_SHELL_PROCESSOR_H

#include <memory>
#include <string>
#include <vector>

namespace elomig {

class FileDiff;

namespace mask {

	/**
	 * @brief Shell script mask processor
	 *
	 * Manages the commenting/uncommenting of mask blocks in shell scripts
	 * to ensure proper diff generation.
	 */
	class ShellProcessor {
	public:
		/**
		 * @brief Default constructor
		 */
		ShellProcessor();

		/**
		 * @brief Prepare a shell file for diffing
		 *
		 * Comments out mask blocks so diff doesn't move them.
		 * Creates a .pwx temporary file.
		 *
		 * @param sourcePath Source file path
		 * @param tempPath Output temporary file path
		 * @return True if preparation succeeded
		 */
		bool prepare( std::string const& sourcePath, std::string& tempPath );

		/**
		 * @brief Unprepare a shell file after diffing
		 *
		 * Restores original mask block comments.
		 *
		 * @param tempPath Temporary .pwx file path
		 * @param originalPath Original file path
		 * @return True if unpreparation succeeded
		 */
		bool unprepare( std::string const& tempPath, std::string const& originalPath );

		/**
		 * @brief Prepare shell content in memory
		 * @param lines Input lines
		 * @param preparedLines Output prepared lines
		 * @return True if preparation succeeded
		 */
		bool prepareContent( std::vector< std::string > const& lines, std::vector< std::string >& preparedLines );

		/**
		 * @brief Unprepare shell content in memory
		 * @param preparedLines Prepared lines
		 * @param originalLines Output original lines
		 * @return True if unpreparation succeeded
		 */
		bool unprepareContent( std::vector< std::string > const& preparedLines, std::vector< std::string >& originalLines );

		/**
		 * @brief Check if a file needs shell preparation
		 * @param filePath File path to check
		 * @return True if file is a shell script needing preparation
		 */
		static bool needsPreparation( std::string const& filePath );

		/**
		 * @brief Get mask block patterns for shell files
		 * @return Vector of regex patterns
		 */
		static std::vector< std::string > const& getMaskPatterns();

	private:
		/**
		 * @brief Comment out a mask line
		 * @param line Line to comment
		 * @return Commented line
		 */
		std::string commentMaskLine( std::string const& line );

		/**
		 * @brief Uncomment a mask line
		 * @param line Line to uncomment
		 * @return Uncommented line
		 */
		std::string uncommentMaskLine( std::string const& line );

		/**
		 * @brief Check if line is a mask directive
		 * @param line Line to check
		 * @return True if line is a mask directive
		 */
		bool                                         isMaskDirective( std::string const& line ) const;

		std::vector< std::pair< int, std::string > > m_originalMasks; ///< Saved mask lines
		bool                                         m_prepared;      ///< Preparation state flag
	};

} // namespace mask
} // namespace elomig

#endif // ELOMIG_SHELL_PROCESSOR_H
