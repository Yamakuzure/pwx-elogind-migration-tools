/**
 * @file CommitDiscovery.h
 * @brief Discover relevant commits for migration
 *
 * Identifies commits in upstream systemd that affect elogind source files
 * and builds the migration timeline.
 */

#ifndef ELOMIG_COMMIT_DISCOVERY_H
#define ELOMIG_COMMIT_DISCOVERY_H

#include "data/CommitInfo.h"

#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

namespace elomig {
namespace migrate {

	/**
	 * @brief Commit discovery manager
	 *
	 * Discovers which upstream commits are relevant to elogind source files
	 * and builds a chronological list of commits to migrate.
	 */
	class CommitDiscovery {
	public:
		/**
		 * @brief Default constructor
		 */
		CommitDiscovery();

		/**
		 * @brief Destructor
		 */
		~CommitDiscovery();

		/**
		 * @brief Set upstream repository path
		 * @param path Path to upstream systemd repository
		 */
		void setUpstreamPath( std::string const& path ) { m_upstreamPath = path; }

		/**
		 * @brief Get upstream repository path
		 * @return Upstream path
		 */
		std::string const& upstreamPath() const { return m_upstreamPath; }

		/**
		 * @brief Set target reference (tag, branch, commit)
		 * @param ref Reference to target
		 */
		void setTargetRef( std::string const& ref ) { m_targetRef = ref; }

		/**
		 * @brief Get target reference
		 * @return Target reference
		 */
		std::string const& targetRef() const { return m_targetRef; }

		/**
		 * @brief Set mutual commit (starting point)
		 * @param commit Mutual commit hash
		 */
		void setMutualCommit( std::string const& commit ) { m_mutualCommit = commit; }

		/**
		 * @brief Get mutual commit
		 * @return Mutual commit hash
		 */
		std::string const& mutualCommit() const { return m_mutualCommit; }

		/**
		 * @brief Set source files list
		 * @param files Vector of source files
		 */
		void setSourceFiles( std::vector< std::string > const& files ) { m_sourceFiles = files; }

		/**
		 * @brief Get source files
		 * @return Vector of source files
		 */
		std::vector< std::string > const& sourceFiles() const { return m_sourceFiles; }

		/**
		 * @brief Discover relevant commits
		 * @return True if successful
		 */
		bool discoverCommits();

		/**
		 * @brief Build chronological commit list
		 * @return True if successful
		 */
		bool buildCommitList();

		/**
		 * @brief Get discovered commits
		 * @return Vector of commit hashes
		 */
		std::vector< std::string > const& commits() const { return m_commits; }

		/**
		 * @brief Get commit details
		 * @param commitHash Commit hash
		 * @return Commit info or empty structure if not found
		 */
		MigrationCommitInfo getCommitInfo( std::string const& commitHash );

		/**
		 * @brief Check if file affects a commit
		 * @param commitHash Commit hash
		 * @param filePath File path
		 * @return True if file affects commit
		 */
		bool fileAffectsCommit( std::string const& commitHash, std::string const& filePath ) const;

	private:
		/**
		 * @brief Build file-to-commit mapping
		 * @return True if successful
		 */
		bool buildFileCommitMapping();

		/**
		 * @brief Check if commit affects source files
		 * @param commitHash Commit hash
		 * @return True if affects source files
		 */
		bool                                             commitAffectsSources( std::string const& commitHash ) const;

		std::string                                      m_upstreamPath;    ///< Upstream repository path
		std::string                                      m_targetRef;       ///< Target reference (tag, branch, commit)
		std::string                                      m_mutualCommit;    ///< Starting mutual commit
		std::vector< std::string >                       m_sourceFiles;     ///< Source files to monitor
		std::vector< std::string >                       m_commits;         ///< Discovered commits
		std::map< std::string, MigrationCommitInfo >     m_commitInfo;      ///< Commit information cache
		std::map< std::string, std::set< std::string > > m_fileCommits;     ///< File-to-commits mapping
		std::set< std::string >                          m_relevantCommits; ///< Set of relevant commits
	};

} // namespace migrate
} // namespace elomig

#endif // ELOMIG_COMMIT_DISCOVERY_H
