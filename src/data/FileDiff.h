/**
 * @file FileDiff.h
 * @brief Data structure representing a complete file diff
 *
 * Contains all hunks for a single file, file paths, and metadata
 * about file type and processing status.
 */

#ifndef ELOMIG_FILE_DIFF_H
#define ELOMIG_FILE_DIFF_H

#include "Hunk.h"

#include <memory>
#include <string>
#include <vector>

namespace elomig {

/**
 * @brief Represents a diff between two versions of a file
 *
 * Manages the source and target file paths, all hunks,
 * and file type information (shell, XML, C, etc.).
 */
class FileDiff {
public:
	/**
	 * @brief Default constructor
	 */
	FileDiff();

	/**
	 * @brief Constructor with file part
	 * @param part Relative file path
	 */
	explicit FileDiff( std::string const& part );

	/**
	 * @brief Get relative file path
	 * @return File part
	 */
	std::string const& part() const { return m_part; }

	/**
	 * @brief Set relative file path
	 * @param part File part
	 */
	void setPart( std::string const& part ) { m_part = part; }

	/**
	 * @brief Get source file path
	 * @return Source path
	 */
	std::string const& sourcePath() const { return m_sourcePath; }

	/**
	 * @brief Set source file path
	 * @param path Source path
	 */
	void setSourcePath( std::string const& path ) { m_sourcePath = path; }

	/**
	 * @brief Get target file path (upstream)
	 * @return Target path
	 */
	std::string const& targetPath() const { return m_targetPath; }

	/**
	 * @brief Set target file path
	 * @param path Target path
	 */
	void setTargetPath( std::string const& path ) { m_targetPath = path; }

	/**
	 * @brief Get patch file path
	 * @return Patch path
	 */
	std::string const& patchPath() const { return m_patchPath; }

	/**
	 * @brief Set patch file path
	 * @param path Patch path
	 */
	void setPatchPath( std::string const& path ) { m_patchPath = path; }

	/**
	 * @brief Check if this is a new file (creation)
	 * @return True if file is being created
	 */
	bool isCreation() const { return m_isCreation; }

	/**
	 * @brief Set creation flag
	 * @param creation True if file is being created
	 */
	void setIsCreation( bool creation ) { m_isCreation = creation; }

	/**
	 * @brief Check if file is a shell script
	 * @return True if shell script
	 */
	bool isShell() const { return m_isShell; }

	/**
	 * @brief Set shell script flag
	 * @param shell True if shell script
	 */
	void setIsShell( bool shell ) { m_isShell = shell; }

	/**
	 * @brief Check if file is XML
	 * @return True if XML file
	 */
	bool isXML() const { return m_isXML; }

	/**
	 * @brief Set XML flag
	 * @param xml True if XML file
	 */
	void setIsXML( bool xml ) { m_isXML = xml; }

	/**
	 * @brief Check if file was prepared (has .pwx temp)
	 * @return True if prepared
	 */
	bool isPrepared() const { return m_isPrepared; }

	/**
	 * @brief Set prepared flag
	 * @param prepared True if prepared
	 */
	void setIsPrepared( bool prepared ) { m_isPrepared = prepared; }

	/**
	 * @brief Get all hunks
	 * @return Vector of hunks
	 */
	std::vector< std::shared_ptr< Hunk > > const& hunks() const { return m_hunks; }

	/**
	 * @brief Get mutable hunks
	 * @return Vector of hunks
	 */
	std::vector< std::shared_ptr< Hunk > >& hunks() { return m_hunks; }

	/**
	 * @brief Add a hunk
	 * @param hunk Hunk to add
	 */
	void addHunk( std::shared_ptr< Hunk > hunk );

	/**
	 * @brief Get hunk count
	 * @return Number of hunks
	 */
	size_t hunkCount() const { return m_hunks.size(); }

	/**
	 * @brief Get hunk at index
	 * @param index Hunk index
	 * @return Shared pointer to hunk
	 */
	std::shared_ptr< Hunk > hunkAt( size_t index ) { return m_hunks[index]; }

	/**
	 * @brief Get hunk at index (const)
	 * @param index Hunk index
	 * @return Const shared pointer to hunk
	 */
	std::shared_ptr< Hunk const > hunkAt( size_t index ) const { return m_hunks[index]; }

	/**
	 * @brief Remove hunk at index
	 * @param index Hunk index
	 */
	void removeHunk( size_t index );

	/**
	 * @brief Clear all hunks
	 */
	void clearHunks();

	/**
	 * @brief Get output lines for final patch
	 * @return Vector of output lines
	 */
	std::vector< std::string > const& output() const { return m_output; }

	/**
	 * @brief Get mutable output lines
	 * @return Vector of output lines
	 */
	std::vector< std::string >& output() { return m_output; }

	/**
	 * @brief Set output lines
	 * @param lines Output lines
	 */
	void setOutput( std::vector< std::string > const& lines ) { m_output = lines; }

	/**
	 * @brief Add line to output
	 * @param line Line to add
	 */
	void addOutputLine( std::string const& line ) { m_output.push_back( line ); }

	/**
	 * @brief Clear output
	 */
	void clearOutput() { m_output.clear(); }

	/**
	 * @brief Count useful hunks
	 * @return Number of hunks with real changes
	 */
	size_t countUsefulHunks() const;

	/**
	 * @brief Check if file has any useful changes
	 * @return True if at least one useful hunk
	 */
	bool hasUsefulChanges() const;

	/**
	 * @brief Build output from useful hunks
	 * @return True if output was built
	 */
	bool buildOutput();

	/**
	 * @brief Get file kind from path
	 * @param path File path
	 * @return File kind string ("shell", "xml", "c", etc.)
	 */
	static std::string getFileKind( std::string const& path );

private:
	std::string                            m_part;       ///< Relative file path
	std::string                            m_sourcePath; ///< Source file path
	std::string                            m_targetPath; ///< Target file path (upstream)
	std::string                            m_patchPath;  ///< Output patch file path
	std::vector< std::shared_ptr< Hunk > > m_hunks;      ///< All hunks
	std::vector< std::string >             m_output;     ///< Final output lines
	bool                                   m_isCreation; ///< True if file is being created
	bool                                   m_isShell;    ///< True if shell script
	bool                                   m_isXML;      ///< True if XML file
	bool                                   m_isPrepared; ///< True if prepared (has .pwx)
};

} // namespace elomig

#endif // ELOMIG_FILE_DIFF_H
