/**
 * @file Patch.h
 * @brief Data structure representing a complete patch
 *
 * Contains patch metadata, file diffs, and application status.
 */

#ifndef ELOMIG_PATCH_H
#define ELOMIG_PATCH_H

#include "FileDiff.h"

#include <memory>
#include <string>
#include <vector>

namespace elomig {

/**
 * @brief Represents a complete patch (potentially multiple files)
 */
class Patch {
public:
	/**
	 * @brief Default constructor
	 */
	Patch();

	/**
	 * @brief Constructor with filename
	 * @param filename Patch filename
	 */
	explicit Patch( std::string const& filename );

	/**
	 * @brief Get patch filename
	 * @return Filename
	 */
	std::string const& filename() const { return m_filename; }

	/**
	 * @brief Set patch filename
	 * @param filename Filename
	 */
	void setFilename( std::string const& filename ) { m_filename = filename; }

	/**
	 * @brief Get commit hash
	 * @return Commit hash
	 */
	std::string const& commitHash() const { return m_commitHash; }

	/**
	 * @brief Set commit hash
	 * @param hash Commit hash
	 */
	void setCommitHash( std::string const& hash ) { m_commitHash = hash; }

	/**
	 * @brief Get patch index
	 * @return Index in patch series
	 */
	int index() const { return m_index; }

	/**
	 * @brief Set patch index
	 * @param index Index
	 */
	void setIndex( int index ) { m_index = index; }

	/**
	 * @brief Check if patch was applied
	 * @return True if applied
	 */
	bool applied() const { return m_applied; }

	/**
	 * @brief Set applied flag
	 * @param applied True if applied
	 */
	void setApplied( bool applied ) { m_applied = applied; }

	/**
	 * @brief Get file diffs in this patch
	 * @return Vector of file diffs
	 */
	std::vector< std::shared_ptr< FileDiff > > const& fileDiffs() const { return m_fileDiffs; }

	/**
	 * @brief Add file diff
	 * @param diff File diff to add
	 */
	void addFileDiff( std::shared_ptr< FileDiff > diff );

	/**
	 * @brief Get patch content as string
	 * @return Patch content
	 */
	std::string content() const { return m_content; }

	/**
	 * @brief Set patch content
	 * @param content Patch content
	 */
	void setContent( std::string const& content ) { m_content = content; }

	/**
	 * @brief Get target files in patch
	 * @return Set of target file paths
	 */
	std::vector< std::string > const& targetFiles() const { return m_targetFiles; }

	/**
	 * @brief Add target file
	 * @param file Target file path
	 */
	void addTargetFile( std::string const& file ) { m_targetFiles.push_back( file ); }

	/**
	 * @brief Check if target file is in patch
	 * @param file File path to check
	 * @return True if file is in patch
	 */
	bool hasTargetFile( std::string const& file ) const;

private:
	std::string                                m_filename;    ///< Patch filename
	std::string                                m_commitHash;  ///< Commit hash
	int                                        m_index;       ///< Patch index
	bool                                       m_applied;     ///< Applied flag
	std::vector< std::shared_ptr< FileDiff > > m_fileDiffs;   ///< File diffs
	std::vector< std::string >                 m_targetFiles; ///< Target files
	std::string                                m_content;     ///< Full patch content
};

} // namespace elomig

#endif // ELOMIG_PATCH_H
