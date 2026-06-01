/**
 * @file CheckTree.h
 * @brief Check tree mode implementation
 *
 * Implements the functionality of check_tree.pl for comparing
 * elogind source tree with upstream systemd.
 */

#ifndef ELOMIG_CHECK_TREE_H
#define ELOMIG_CHECK_TREE_H

#include "data/FileDiff.h"
#include "utils/ThreadPool.h"

#include <memory>
#include <string>
#include <thread>
#include <vector>

namespace elomig {
namespace checktree {

	/**
	 * @brief Main class for check tree operations
	 *
	 * This class implements the core functionality of check_tree.pl, comparing
	 * elogind source tree with upstream systemd to identify differences and generate patches.
	 * It handles repository management, file processing, diff generation, and patch creation.
	 *
	 * The CheckTree class orchestrates the comparison process between two code bases,
	 * generating unified diffs and patches that can be used for migration purposes.
	 * It supports various modes including debug output, parallel processing, and
	 * selective file processing.
	 *
	 * @ingroup CheckTree
	 */
	class CheckTree {
	public:
		/**
		 * @brief Default constructor
		 */
		CheckTree();

		/**
		 * @brief Destructor
		 */
		~CheckTree();

		/**
		 * @brief Set upstream path
		 * @param path Path to upstream systemd tree
		 */
		void setUpstreamPath( std::string const& path ) { m_upstreamPath = path; }

		/**
		 * @brief Get upstream path
		 * @return Upstream path
		 */
		std::string const& upstreamPath() const { return m_upstreamPath; }

		/**
		 * @brief Set commit to checkout
		 * @param commit Commit hash or reference
		 */
		void setCommit( std::string const& commit ) { m_commit = commit; }

		/**
		 * @brief Get commit
		 * @return Commit reference
		 */
		std::string const& commit() const { return m_commit; }

		/**
		 * @brief Set stay flag (don't restore HEAD)
		 * @param stay True to stay at commit
		 */
		void setStay( bool stay ) { m_stay = stay; }

		/**
		 * @brief Get stay flag
		 * @return Stay flag
		 */
		bool stay() const { return m_stay; }

		/**
		 * @brief Set debug mode
		 * @param debug True to enable debug output
		 */
		void setDebugMode( bool debug ) { m_debugMode = debug; }

		/**
		 * @brief Get debug mode
		 * @return Debug mode flag
		 */
		bool debugMode() const { return m_debugMode; }

		/**
		 * @brief Set create mode (allow new files)
		 * @param create True to allow creation
		 */
		void setCreateMode( bool create ) { m_createMode = create; }

		/**
		 * @brief Get create mode
		 * @return Create mode flag
		 */
		bool createMode() const { return m_createMode; }

		/**
		 * @brief Set source path
		 * @param path Source directory path
		 */
		void setSourcePath( std::string const& path ) { m_sourcePath = path; }

		/**
		 * @brief Get source path
		 * @return Source path
		 */
		std::string const& sourcePath() const { return m_sourcePath; }

		/**
		 * @brief Set thread count for parallel processing
		 * @param count Number of threads to use
		 */
		void setThreadCount( size_t count ) { m_threadCount = count; }

		/**
		 * @brief Get thread count
		 * @return Thread count
		 */
		size_t threadCount() const { return m_threadCount; }

		/**
		 * @brief Add file to process
		 * @param file File path
		 */
		void addFile( std::string const& file ) { m_files.push_back( file ); }

		/**
		 * @brief Get files to process
		 * @return Vector of file paths
		 */
		std::vector< std::string > const& files() const { return m_files; }

		/**
		 * @brief Run check tree operation
		 * @return True if successful
		 */
		bool run();

		/**
		 * @brief Get processed file diffs
		 * @return Vector of file diffs
		 */
		std::vector< std::shared_ptr< FileDiff > > const& fileDiffs() const { return m_fileDiffs; }

	private:
		/**
		 * @brief Resolve source directory
		 * @return True if successful
		 */
		bool resolveSourceDir();

		/**
		 * @brief Generate file list
		 * @return True if successful
		 */
		bool generateFileList();

		/**
		 * @brief Checkout upstream commit
		 * @return True if successful
		 */
		bool checkoutUpstream();

		/**
		 * @brief Process a single file
		 * @param filePart Relative file path
		 * @return True if processed
		 */
		bool processFile( std::string const& filePart );

		/**
		 * @brief Process files in parallel
		 * @param files Vector of file paths to process
		 * @return True if successful
		 */
		bool processFilesParallel( std::vector< std::string > const& files );

		/**
		 * @brief Generate diff for file
		 * @param fileDiff File diff object
		 * @return True if diff generated
		 */
		bool generateDiff( std::shared_ptr< FileDiff > fileDiff );

		/**
		 * @brief Refactor hunks
		 * @param fileDiff File diff to refactor
		 * @return True if successful
		 */
		bool refactorHunks( std::shared_ptr< FileDiff > fileDiff );

		/**
		 * @brief Build and write patch
		 * @param fileDiff File diff
		 * @return True if patch written
		 */
		bool                                       writePatch( std::shared_ptr< FileDiff > fileDiff );

		std::string                                m_upstreamPath;   ///< Upstream tree path
		std::string                                m_commit;         ///< Commit to checkout
		std::string                                m_sourcePath;     ///< Source directory
		std::string                                m_resolvedSource; ///< Resolved source path
		std::vector< std::string >                 m_files;          ///< Files to process
		std::vector< std::string >                 m_allFiles;       ///< All files (if no specific files)
		std::vector< std::shared_ptr< FileDiff > > m_fileDiffs;      ///< Processed diffs
		size_t                                     m_threadCount;    ///< Number of threads to use
		bool                                       m_stay;           ///< Stay at commit flag
		bool                                       m_debugMode;      ///< Debug mode
		bool                                       m_createMode;     ///< Create mode
		std::string                                m_previousCommit; ///< Previous upstream commit
		std::vector< std::string >                 m_onlyHere;       ///< Files only in local tree
		std::unique_ptr< ThreadPool >              m_threadPool;     ///< Thread pool for parallel processing
	};

} // namespace checktree
} // namespace elomig

#endif // ELOMIG_CHECK_TREE_H
