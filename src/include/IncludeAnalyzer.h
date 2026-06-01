/**
 * @file IncludeAnalyzer.h
 * @brief Analyze include directives in hunks
 *
 * Detects and categorizes #include statements in hunks to handle
 * elogind-specific include requirements and conflicts.
 */

#ifndef ELOMIG_INCLUDE_ANALYZER_H
#define ELOMIG_INCLUDE_ANALYZER_H

#include <map>
#include <memory>
#include <string>
#include <vector>

namespace elomig {

class Hunk;
class HunkLine;

namespace include {

	/**
	 * @brief Information about an include directive
	 */
	struct IncludeInfo {
		std::string fileName;   ///< Include file name
		std::string directive;  ///< Complete include directive (e.g., "#include <stdio.h>")
		std::string type;       ///< Include type ("system", "local")
		bool        isAdded;    ///< True if added to source
		bool        isRemoved;  ///< True if removed from source
		bool        isEligible; ///< True if eligible for protection
		bool        isElogind;  ///< True if elogind-specific include
		bool        isSpliceMe; ///< True if should be spliced out

		IncludeInfo() : isAdded( false ), isRemoved( false ), isEligible( false ), isElogind( false ), isSpliceMe( false ) {}
	};

	/**
	 * @brief Include analyzer for hunk processing
	 *
	 * Analyzes hunks for include directive changes and identifies
	 * conflicts and elogind-specific requirements.
	 */
	class IncludeAnalyzer {
	public:
		/**
		 * @brief Default constructor
		 */
		IncludeAnalyzer();

		/**
		 * @brief Analyze a hunk for include directives
		 * @param hunk Hunk to analyze
		 * @return True if includes found
		 */
		bool analyzeHunk( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Get include information by line index
		 * @param lineIndex Index of line to check
		 * @return IncludeInfo if line contains include, {} otherwise
		 */
		IncludeInfo getIncludeInfo( int lineIndex ) const;

		/**
		 * @brief Check if a line is an include directive
		 * @param line Hunk line to check
		 * @return True if line contains include directive
		 */
		static bool isIncludeDirective( std::string const& line );

		/**
		 * @brief Extract include file name
		 * @param line Line containing include directive
		 * @return Include file name
		 */
		static std::string extractIncludeFile( std::string const& line );

		/**
		 * @brief Check if include is elogind-specific
		 * @param fileName Include file name
		 * @return True if elogind-specific
		 */
		static bool isElogindInclude( std::string const& fileName );

		/**
		 * @brief Check if include type is system (brackets) or local (quotes)
		 * @param line Line containing include directive
		 * @return "system" or "local"
		 */
		static std::string getIncludeType( std::string const& line );

	private:
		/**
		 * @brief Extract include info from line
		 * @param line Hunk line
		 * @param lineIndex Line index
		 * @return IncludeInfo structure
		 */
		IncludeInfo                  extractIncludeInfo( HunkLine const& line, int lineIndex );

		std::map< int, IncludeInfo > m_includeMap; ///< Map of line index to include info
	};

} // namespace include
} // namespace elomig

#endif // ELOMIG_INCLUDE_ANALYZER_H
