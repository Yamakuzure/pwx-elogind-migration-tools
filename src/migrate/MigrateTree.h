/**
 * @file MigrateTree.h
 * @brief Main migration tree class
 *
 * Implements the complete migrate_tree functionality for automated
 * commit migration from systemd to elogind.
 */

#ifndef ELOMIG_MIGRATE_TREE_H
#define ELOMIG_MIGRATE_TREE_H

#include <memory>
#include <set>
#include <string>
#include <vector>

namespace elomig {
namespace migrate {

	class CommitDiscovery;
	class PatchGenerator;
	class PatchApplier;
	class CommitFile;

	/**
	 * @brief Main migration manager
	 *
	 * Orchestrates the complete migration process from upstream commits to elogind.
	 * This class manages the coordination between commit discovery, patch generation,
	 * and patch application phases of the migration workflow.
	 *
	 * The migration process involves discovering relevant commits from upstream,
	 * generating patches for each commit, and applying those patches to elogind.
	 *
	 * @ingroup MigrateTree
	 */
	class MigrateTree {
	public:
		/**
		 * @brief Default constructor
		 */
		MigrateTree();

		/**
		 * @brief Destructor
		 */
		~MigrateTree();

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
		 * @brief Set elogind repository path
		 * @param path Path to elogind repository
		 */
		void setElogindPath( std::string const& path ) { m_elogindPath = path; }

		/**
		 * @brief Get elogind repository path
		 * @return Elogind path
		 */
		std::string const& elogindPath() const { return m_elogindPath; }

		/**
		 * @brief Set target reference (tag, branch, commit)
		 * @param ref Target reference
		 */
		void setRefId( std::string const& ref ) { m_refId = ref; }

		/**
		 * @brief Get target reference
		 * @return Target reference
		 */
		std::string const& refId() const { return m_refId; }

		/**
		 * @brief Set advance flag (use last src commit as new mutual)
		 * @param advance True to enable advance mode
		 */
		void setAdvance( bool advance ) { m_advance = advance; }

		/**
		 * @brief Get advance flag
		 * @return Advance flag
		 */
		bool advance() const { return m_advance; }

		/**
		 * @brief Set explicit mutual commit
		 * @param commit Mutual commit hash
		 */
		void setMutualCommit( std::string const& commit ) { m_mutualCommit = commit; }

		/**
		 * @brief Get mutual commit
		 * @return Mutual commit hash
		 */
		std::string const& mutualCommit() const { return m_mutualCommit; }

		/**
		 * @brief Set output directory for patches
		 * @param path Output directory path
		 */
		void setOutputPath( std::string const& path ) { m_outputPath = path; }

		/**
		 * @brief Get output directory
		 * @return Output directory
		 */
		std::string const& outputPath() const { return m_outputPath; }

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
		 * @brief Run migration process
		 *
		 * Executes the complete migration workflow from discovering commits to
		 * applying patches to the elogind repository. This is the main entry point
		 * for the migration process.
		 *
		 * The process follows these steps:
		 * 1. Discover relevant commits from upstream
		 * 2. Generate patches for each commit
		 * 3. Apply patches to elogind repository
		 *
		 * @retval bool True if migration completed successfully, false otherwise
		 *
		 * @note This method coordinates all phases of migration and handles cleanup
		 * @note The operation may take considerable time depending on the number of commits
		 *
		 * @see discoverCommits()
		 * @see generatePatches()
		 * @see applyPatches()
		 */
		bool run();

		/**
		 * @brief Discover relevant commits
		 *
		 * Discovers commits from upstream systemd that are relevant for migration
		 * to elogind. This involves identifying commits that have not yet been
		 * migrated to elogind and determining the correct commit history to follow.
		 *
		 * @retval bool True if commits were discovered successfully, false otherwise
		 *
		 * @note This method populates internal data structures with commit information
		 * @note The discovery process considers mutual commits to establish the baseline
		 *
		 * @see run()
		 * @see generatePatches()
		 */
		bool discoverCommits();

		/**
		 * @brief Generate patches for commits
		 *
		 * Generates unified diff patches for each discovered commit. These patches
		 * represent the changes needed to migrate from upstream to elogind.
		 *
		 * @retval bool True if patches were generated successfully, false otherwise
		 *
		 * @note This method creates patch files in the configured output directory
		 * @note Each patch corresponds to a specific upstream commit
		 *
		 * @see run()
		 * @see discoverCommits()
		 * @see applyPatches()
		 */
		bool generatePatches();

		/**
		 * @brief Apply patches to elogind repository
		 * @return True if successful
		 */
		bool applyPatches();

		/**
		 * @brief Update mutual commit tracking
		 * @return True if successful
		 */
		bool updateMutualCommits();

		/**
		 * @brief Get generated patches
		 * @return Vector of generated patch paths
		 */
		std::vector< std::string > const& generatedPatches() const { return m_generatedPatches; }

		/**
		 * @brief Get applied patches
		 * @return Vector of applied patch paths
		 */
		std::vector< std::string > const& appliedPatches() const { return m_appliedPatches; }

	private:
		/**
		 * @brief Initialize source file list
		 * @return True if successful
		 */
		bool initializeSourceFiles();

		/**
		 * @brief Prepare working environment
		 * @return True if successful
		 */
		bool prepareEnvironment();

		/**
		 * @brief Cleanup temporary files
		 * @return True if successful
		 */
		bool cleanupTempFiles();

		/**
		 * @brief Checkout upstream repository
		 * @return True if successful
		 */
		bool checkoutUpstream();

		/**
		 * @brief Restore upstream to original state
		 * @return True if successful
		 */
		bool                       restoreUpstream();

		std::string                m_upstreamPath;     ///< Upstream systemd repository path
		std::string                m_elogindPath;      ///< Elogind repository path
		std::string                m_refId;            ///< Target reference (tag, branch, commit)
		std::string                m_mutualCommit;     ///< Starting mutual commit
		std::string                m_outputPath;       ///< Output directory for patches
		std::vector< std::string > m_sourceFiles;      ///< Source files to track
		std::vector< std::string > m_generatedPatches; ///< Generated patch files
		std::vector< std::string > m_appliedPatches;   ///< Applied patch files
		bool                       m_advance;          ///< Advance mode flag
		bool                       m_debugMode;        ///< Debug mode flag
		bool                       m_commitsRead;      ///< Flag indicating if commits were read
		std::string                m_previousRefId;    ///< Previous upstream ref for restoration

		// Component managers
		std::unique_ptr< CommitDiscovery > m_commitDiscovery; ///< Commit discovery manager
		std::unique_ptr< PatchGenerator >  m_patchGenerator;  ///< Patch generator
		std::unique_ptr< PatchApplier >    m_patchApplier;    ///< Patch applier
		std::unique_ptr< CommitFile >      m_commitFile;      ///< Commit file manager
	};

} // namespace migrate
} // namespace elomig

#endif // ELOMIG_MIGRATE_TREE_H
