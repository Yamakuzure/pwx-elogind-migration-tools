/**
 * @file Hunk.h
 * @brief Data structure representing a unified diff hunk
 *
 * A hunk is a contiguous block of changes in a diff, containing
 * context lines, additions, and removals.
 */

#ifndef ELOMIG_HUNK_H
#define ELOMIG_HUNK_H

#include <cstdint>
#include <string>
#include <vector>

namespace elomig {

/**
 * @brief Line type in a hunk
 */
enum class LineType {
	CONTEXT  = 0, ///< Unchanged context line (prefix: ' ')
	ADDITION = 1, ///< Added line (prefix: '+')
	REMOVAL  = -1 ///< Removed line (prefix: '-')
};

/**
 * @brief Single line in a hunk
 */
struct HunkLine {
	LineType    type;        ///< Type of line
	std::string content;     ///< Line content (without prefix)
	std::string original;    ///< Original line with prefix
	int         lineNumber;  ///< Line number in hunk
	bool        masked;      ///< True if line is inside mask block
	bool        isComment;   ///< True if line is a comment
	bool        done;        ///< True if line has been processed
	int         partner;     ///< Index of partner line (-1 if none)
	int         spliceIndex; ///< Index for splicing (-1 if not marked)

	HunkLine() : type( LineType::CONTEXT ), lineNumber( 0 ), masked( false ), isComment( false ), done( false ), partner( -1 ), spliceIndex( -1 ) {}
};

/**
 * @brief Represents a single hunk in a unified diff
 *
 * Contains all lines in the hunk, position information,
 * and metadata about mask blocks and usefulness.
 */
class Hunk {
public:
	/**
	 * @brief Default constructor
	 */
	Hunk();

	/**
	 * @brief Get number of lines in hunk
	 * @return Line count
	 */
	size_t lineCount() const { return m_lines.size(); }

	/**
	 * @brief Get all lines
	 * @return Vector of lines
	 */
	std::vector< HunkLine > const& lines() const { return m_lines; }

	/**
	 * @brief Get mutable lines
	 * @return Vector of lines
	 */
	std::vector< HunkLine >& lines() { return m_lines; }

	/**
	 * @brief Get line at index
	 * @param index Line index
	 * @return Reference to line
	 */
	HunkLine& lineAt( size_t index ) { return m_lines[index]; }

	/**
	 * @brief Get line at index (const)
	 * @param index Line index
	 * @return Const reference to line
	 */
	HunkLine const& lineAt( size_t index ) const { return m_lines[index]; }

	/**
	 * @brief Add a line to the hunk
	 * @param line Line to add
	 */
	void addLine( HunkLine const& line );

	/**
	 * @brief Remove line at index
	 * @param index Line index
	 */
	void removeLine( size_t index );

	/**
	 * @brief Insert line at position
	 * @param index Position to insert
	 * @param line Line to insert
	 */
	void insertLine( size_t index, HunkLine const& line );

	/**
	 * @brief Get source file start line
	 * @return Start line number in source
	 */
	int sourceStart() const { return m_srcStart; }

	/**
	 * @brief Set source file start line
	 * @param start Start line number
	 */
	void setSourceStart( int start ) { m_srcStart = start; }

	/**
	 * @brief Get target file start line
	 * @return Start line number in target
	 */
	int targetStart() const { return m_tgtStart; }

	/**
	 * @brief Set target file start line
	 * @param start Start line number
	 */
	void setTargetStart( int start ) { m_tgtStart = start; }

	/**
	 * @brief Get hunk index in file
	 * @return Hunk index
	 */
	int index() const { return m_index; }

	/**
	 * @brief Set hunk index
	 * @param idx Hunk index
	 */
	void setIndex( int idx ) { m_index = idx; }

	/**
	 * @brief Check if hunk is useful (has real changes)
	 * @return True if hunk should be included in patch
	 */
	bool isUseful() const { return m_useful; }

	/**
	 * @brief Set hunk usefulness flag
	 * @param useful True if hunk is useful
	 */
	void setUseful( bool useful ) { m_useful = useful; }

	/**
	 * @brief Check if hunk starts in mask block
	 * @return True if masked start
	 */
	bool maskedStart() const { return m_maskedStart; }

	/**
	 * @brief Set masked start flag
	 * @param masked True if starts in mask
	 */
	void setMaskedStart( bool masked ) { m_maskedStart = masked; }

	/**
	 * @brief Check if hunk ends in mask block
	 * @return True if masked end
	 */
	bool maskedEnd() const { return m_maskedEnd; }

	/**
	 * @brief Set masked end flag
	 * @param masked True if ends in mask
	 */
	void setMaskedEnd( bool masked ) { m_maskedEnd = masked; }

	/**
	 * @brief Get offset adjustment
	 * @return Offset value
	 */
	int offset() const { return m_offset; }

	/**
	 * @brief Set offset adjustment
	 * @param offset Offset value
	 */
	void setOffset( int offset ) { m_offset = offset; }

	/**
	 * @brief Generate unified diff header for this hunk
	 * @param offsetRef Reference to running offset
	 * @return Header string (e.g., "@@ -100,5 +100,7 @@")
	 */
	std::string generateHeader( int& offsetRef ) const;

	/**
	 * @brief Count additions in hunk
	 * @return Number of addition lines
	 */
	size_t countAdditions() const;

	/**
	 * @brief Count removals in hunk
	 * @return Number of removal lines
	 */
	size_t countRemovals() const;

	/**
	 * @brief Check if hunk has any real changes
	 * @return True if hunk has additions or removals
	 */
	bool hasChanges() const;

	/**
	 * @brief Convert hunk to output lines
	 * @param includeHeader If true, include @@ header
	 * @param offsetRef Reference to running offset
	 * @return Vector of output lines
	 */
	std::vector< std::string > toOutput( bool includeHeader = true, int offsetRef = 0 ) const;

private:
	std::vector< HunkLine > m_lines;       ///< Lines in hunk
	int                     m_srcStart;    ///< Source file start line
	int                     m_tgtStart;    ///< Target file start line
	int                     m_index;       ///< Hunk index in file
	bool                    m_useful;      ///< True if hunk has real changes
	bool                    m_maskedStart; ///< True if starts in mask block
	bool                    m_maskedEnd;   ///< True if ends in mask block
	int                     m_offset;      ///< Offset adjustment
};

} // namespace elomig

#endif // ELOMIG_HUNK_H
