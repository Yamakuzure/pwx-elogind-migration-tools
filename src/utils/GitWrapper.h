/**
 * @file GitWrapper.h
 * @brief Git repository operations wrapper using libgit2
 *
 * Provides high-level Git operations needed for commit discovery,
 * checkout, and patch generation.
 */

#ifndef ELOMIG_GIT_WRAPPER_H
#define ELOMIG_GIT_WRAPPER_H

#include <git2.h>
#include <memory>
#include <string>
#include <vector>

namespace elomig {

/**
 * @brief Structure holding commit information
 */
struct CommitInfo {
	std::string hash;      ///< Full commit hash
	std::string shortHash; ///< Short hash (7-10 chars)
	std::string message;   ///< Commit message (first line)
	std::string author;    ///< Author name
	std::string email;     ///< Author email
	git_time_t  time;      ///< Commit time
	int         timezone;  ///< Timezone offset
};

/**
 * @brief Wrapper class for libgit2 operations
 *
 * Provides RAII-style management of libgit2 resources and
 * high-level operations for repository manipulation.
 */
class GitWrapper {
public:
	/**
	 * @brief Constructor
	 * @param repoPath Path to the Git repository
	 */
	explicit GitWrapper( std::string const& repoPath );

	/**
	 * @brief Destructor
	 */
	~GitWrapper();

	// Delete copy constructor and assignment
	GitWrapper( GitWrapper const& )             = delete;
	GitWrapper& operator= ( GitWrapper const& ) = delete;

	/**
	 * @brief Check if repository opened successfully
	 * @return True if repository is valid
	 */
	bool isValid() const { return m_repo != nullptr; }

	/**
	 * @brief Get the current HEAD commit hash
	 * @return Short hash of current HEAD, or empty string on error
	 */
	std::string getHeadCommit() const;

	/**
	 * @brief Get commit hash for a reference
	 * @param ref Reference name (branch, tag, or commit hash)
	 * @return Full commit hash, or empty string on error
	 */
	std::string resolveRef( std::string const& ref ) const;

	/**
	 * @brief Get short hash for a commit
	 * @param ref Reference or commit hash
	 * @return Short hash (7-10 chars)
	 */
	std::string getShortHash( std::string const& ref ) const;

	/**
	 * @brief Checkout a commit/branch/tag
	 * @param ref Reference to checkout
	 * @return True if checkout succeeded
	 */
	bool checkout( std::string const& ref );

	/**
	 * @brief Get list of commits between two references
	 * @param from Starting reference (exclusive)
	 * @param to Ending reference (inclusive)
	 * @param path Optional path to limit commits to
	 * @param noMerges If true, exclude merge commits
	 * @param reverse If true, return in chronological order
	 * @return Vector of commit hashes
	 */
	std::vector< std::string >
		revList( std::string const& from, std::string const& to, std::string const& path = "", bool noMerges = true, bool reverse = false ) const;

	/**
	 * @brief Get commits that touch a specific file
	 * @param from Starting reference
	 * @param to Ending reference
	 * @param filePath Path to file
	 * @return Vector of commit hashes
	 */
	std::vector< std::string > getFileCommits( std::string const& from, std::string const& to, std::string const& filePath ) const;

	/**
	 * @brief Get commit information
	 * @param hash Commit hash
	 * @return CommitInfo structure, or empty struct on error
	 */
	CommitInfo getCommitInfo( std::string const& hash ) const;

	/**
	 * @brief Get commit message
	 * @param hash Commit hash
	 * @return Commit message (first line)
	 */
	std::string getCommitMessage( std::string const& hash ) const;

	/**
	 * @brief Check if a reference exists
	 * @param ref Reference name
	 * @return True if reference exists
	 */
	bool refExists( std::string const& ref ) const;

	/**
	 * @brief Get current branch name
	 * @return Branch name, or empty string if detached HEAD
	 */
	std::string getCurrentBranch() const;

	/**
	 * @brief Check if repository is in clean state
	 * @return True if no uncommitted changes
	 */
	bool isClean() const;

	/**
	 * @brief Get path to repository
	 * @return Repository path
	 */
	std::string const& getRepoPath() const { return m_repoPath; }

private:
	/**
	 * @brief Initialize libgit2 (called once)
	 */
	static void initializeLibGit2();

	/**
	 * @brief Cleanup libgit2 (called on program exit)
	 */
	static void     cleanupLibGit2();

	git_repository* m_repo;        ///< libgit2 repository handle
	std::string     m_repoPath;    ///< Path to repository

	static bool     s_initialized; ///< libgit2 initialization flag
};

/**
 * @brief Generate format-patch output for a commit
 * @param repoPath Path to repository
 * @param commitHash Commit to generate patch for
 * @param outputDir Directory to write patch files
 * @param startNumber Starting patch number
 * @return Vector of generated patch file names
 */
std::vector< std::string > generateFormatPatch( std::string const& repoPath, std::string const& commitHash, std::string const& outputDir, int startNumber = 1 );

/**
 * @brief Apply a patch using git am
 * @param repoPath Path to repository
 * @param patchContent Patch content
 * @param threeWay If true, use 3-way merge
 * @return True if patch applied successfully
 */
bool applyPatch( std::string const& repoPath, std::string const& patchContent, bool threeWay = true );

/**
 * @brief Add files to Git index
 * @param repoPath Path to repository
 * @param files Vector of file paths to add
 * @return True if all files added successfully
 */
bool gitAdd( std::string const& repoPath, std::vector< std::string > const& files );

} // namespace elomig

#endif // ELOMIG_GIT_WRAPPER_H
