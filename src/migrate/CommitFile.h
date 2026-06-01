/**
 * @file CommitFile.h
 * @brief Handle mutual commit tracking CSV file
 *
 * Manages the storage and retrieval of mutual commit information
 * for tracking migration progress.
 */

#ifndef ELOMIG_COMMIT_FILE_H
#define ELOMIG_COMMIT_FILE_H

#include "data/CommitInfo.h"

#include <map>
#include <memory>
#include <string>
#include <vector>

namespace elomig {
namespace migrate {

	/**
	 * @brief Commit file manager
	 *
	 * Handles reading and writing of the mutual commit tracking CSV file
	 * that records migration progress.
	 */
	class CommitFile {
	public:
		/**
		 * @brief Default constructor
		 */
		CommitFile();

		/**
		 * @brief Destructor
		 */
		~CommitFile();

		/**
		 * @brief Set CSV file path
		 * @param path Path to CSV file
		 */
		void setFilePath( std::string const& path ) { m_filePath = path; }

		/**
		 * @brief Get CSV file path
		 * @return CSV file path
		 */
		std::string const& filePath() const { return m_filePath; }

		/**
		 * @brief Read mutual commits from CSV file
		 * @return True if successful
		 */
		bool readMutualCommits();

		/**
		 * @brief Write mutual commits to CSV file
		 * @return True if successful
		 */
		bool writeMutualCommits();

		/**
		 * @brief Get mutual commit entry
		 * @param upstreamPath Upstream repository path
		 * @param refId Reference ID
		 * @return Mutual commit entry or empty if not found
		 */
		MutualCommitEntry getMutualCommit( std::string const& upstreamPath, std::string const& refId ) const;

		/**
		 * @brief Set mutual commit entry
		 * @param upstreamPath Upstream repository path
		 * @param refId Reference ID
		 * @param entry Mutual commit entry
		 */
		void setMutualCommit( std::string const& upstreamPath, std::string const& refId, MutualCommitEntry const& entry );

		/**
		 * @brief Update mutual commit tracking
		 * @param upstreamPath Upstream repository path
		 * @param refId Reference ID
		 * @param mutualHash Mutual commit hash
		 * @param srcHash Source commit hash
		 * @param tgtHash Target commit hash
		 * @return True if successful
		 */
		bool updateMutualCommit(
			std::string const& upstreamPath,
			std::string const& refId,
			std::string const& mutualHash,
			std::string const& srcHash,
			std::string const& tgtHash
		);

		/**
		 * @brief Get all mutual commits
		 * @return Map of all mutual commits
		 */
		std::map< std::string, MutualCommitEntry > const& mutualCommits() const { return m_mutualCommits; }

	private:
		/**
		 * @brief Parse CSV line
		 * @param line CSV line to parse
		 * @return Mutual commit entry or empty if parsing failed
		 */
		MutualCommitEntry parseCsvLine( std::string const& line ) const;

		/**
		 * @brief Format CSV line
		 * @param entry Mutual commit entry to format
		 * @return Formatted CSV line
		 */
		std::string                                formatCsvLine( MutualCommitEntry const& entry ) const;

		std::string                                m_filePath;      ///< CSV file path
		std::map< std::string, MutualCommitEntry > m_mutualCommits; ///< Loaded mutual commits
		bool                                       m_commitsRead;   ///< Flag indicating if commits were read
	};

} // namespace migrate
} // namespace elomig

#endif // ELOMIG_COMMIT_FILE_H
