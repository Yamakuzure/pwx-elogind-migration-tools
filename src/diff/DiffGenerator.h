/**
 * @file DiffGenerator.h
 * @brief Unified diff generation
 */

#ifndef ELOMIG_DIFF_GENERATOR_H
#define ELOMIG_DIFF_GENERATOR_H

#include <string>
#include <vector>

namespace elomig {

/**
 * @brief Generates unified diffs between files
 */
class DiffGenerator {
public:
	DiffGenerator() = default;

	/**
	 * @brief Generate unified diff between two files
	 * @param sourcePath Source file path
	 * @param targetPath Target file path
	 * @param label File label for diff header
	 * @return Unified diff output, or empty if no differences
	 */
	std::string generateUnifiedDiff( std::string const& sourcePath, std::string const& targetPath, std::string const& label );

	/**
	 * @brief Generate diff with context lines
	 * @param sourceLines Source file lines
	 * @param targetLines Target file lines
	 * @param contextLines Number of context lines
	 * @return Vector of diff hunks
	 */
	std::vector< std::string > generateDiff( std::vector< std::string > const& sourceLines, std::vector< std::string > const& targetLines, int contextLines = 3 );

private:
	/**
	 * @brief Run external diff command
	 * @param source Source file
	 * @param target Target file
	 * @return Diff output
	 */
	std::string runExternalDiff( std::string const& source, std::string const& target );
};

} // namespace elomig

#endif // ELOMIG_DIFF_GENERATOR_H
