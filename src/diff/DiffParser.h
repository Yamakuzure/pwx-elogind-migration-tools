/**
 * @file DiffParser.h
 * @brief Parse unified diff output
 */

#ifndef ELOMIG_DIFF_PARSER_H
#define ELOMIG_DIFF_PARSER_H

#include "data/FileDiff.h"

#include <memory>
#include <string>
#include <vector>

namespace elomig {

/**
 * @brief Parses unified diff output into FileDiff structure
 */
class DiffParser {
public:
	DiffParser() = default;

	/**
	 * @brief Parse diff output
	 * @param diffOutput Unified diff text
	 * @param fileDiff FileDiff to populate
	 * @return True if parsing succeeded
	 */
	bool parse( std::string const& diffOutput, std::shared_ptr< FileDiff > fileDiff );

	/**
	 * @brief Parse a single hunk
	 * @param lines Hunk lines
	 * @param hunk Hunk object to populate
	 * @return True if parsing succeeded
	 */
	bool parseHunk( std::vector< std::string > const& lines, std::shared_ptr< Hunk > hunk );

private:
	/**
	 * @brief Parse hunk header
	 * @param header Header line (e.g., "@@ -100,5 +100,7 @@")
	 * @param srcStart Output: source start line
	 * @param tgtStart Output: target start line
	 * @return True if header is valid
	 */
	bool parseHunkHeader( std::string const& header, int& srcStart, int& tgtStart );

	/**
	 * @brief Parse line type from prefix
	 * @param line Line with prefix
	 * @param type Output: line type
	 * @param content Output: line content without prefix
	 * @return True if valid
	 */
	bool parseLineType( std::string const& line, LineType& type, std::string& content );
};

} // namespace elomig

#endif // ELOMIG_DIFF_PARSER_H
