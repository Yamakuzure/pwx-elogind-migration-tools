/**
 * @file PatchGenerator.h
 * @brief Generate formatted patches for migration
 *
 * Creates git format-patch output and processes it for elogind compatibility.
 */

#ifndef ELOMIG_PATCH_GENERATOR_H
#define ELOMIG_PATCH_GENERATOR_H

#include "data/Patch.h"

#include <memory>
#include <string>
#include <vector>

namespace elomig {
namespace migrate {

	/**
	 * @brief Patch generator for migration
	 *
	 * Generates formatted patches for commits and processes them for elogind compatibility.
	 */
	class PatchGenerator {
	public:
		/**
		 * @brief Default constructor
		 */
		PatchGenerator();

		/**
		 * @brief Destructor
		 */
		~PatchGenerator();

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
		 * @brief Set output directory
		 * @param path Output directory path
		 */
		void setOutputPath( std::string const& path ) { m_outputPath = path; }

		/**
		 * @brief Get output directory
		 * @return Output directory
		 */
		std::string const& outputPath() const { return m_outputPath; }

		/**
		 * @brief Set starting commit
		 * @param commit Starting commit hash
		 */
		void setStartCommit( std::string const& commit ) { m_startCommit = commit; }

		/**
		 * @brief Get starting commit
		 * @return Starting commit
		 */
		std::string const& startCommit() const { return m_startCommit; }

		/**
		 * @brief Set target commit
		 * @param commit Target commit hash
		 */
		void setTargetCommit( std::string const& commit ) { m_targetCommit = commit; }

		/**
		 * @brief Get target commit
		 * @return Target commit
		 */
		std::string const& targetCommit() const { return m_targetCommit; }

		/**
		 * @brief Generate patches for commit
		 * @param commitHash Commit hash
		 * @param patchNumber Patch number
		 * @return Generated patch files or empty vector if failed
		 */
		std::vector< std::string > generateCommitPatches( std::string const& commitHash, int patchNumber );

		/**
		 * @brief Generate patches for commit range
		 * @param startCommit Starting commit
		 * @param endCommit Ending commit
		 * @param patchNumber Starting patch number
		 * @return Generated patch files or empty vector if failed
		 */
		std::vector< std::string > generateCommitRangePatches( std::string const& startCommit, std::string const& endCommit, int patchNumber = 1 );

		/**
		 * @brief Process and rework patches using check_tree logic
		 * @param patchFiles Vector of patch files to process
		 * @return True if successful
		 */
		bool reworkPatches( std::vector< std::string > const& patchFiles );

		/**
		 * @brief Get generated patches
		 * @return Vector of generated patch file paths
		 */
		std::vector< std::string > const& generatedPatches() const { return m_generatedPatches; }

	private:
		/**
		 * @brief Generate patches via git format-patch
		 * @param commitHash Commit to generate patch for
		 * @param patchNumber Patch number
		 * @return Generated patch file or empty string if failed
		 */
		std::string generateFormatPatch( std::string const& commitHash, int patchNumber );

		/**
		 * @brief Apply check_tree.pl logic to patch
		 * @param patchFile Patch file to rework
		 * @return True if successful
		 */
		bool                       reworkSinglePatch( std::string const& patchFile );

		std::string                m_upstreamPath;     ///< Upstream repository path
		std::string                m_outputPath;       ///< Output directory
		std::string                m_startCommit;      ///< Starting commit
		std::string                m_targetCommit;     ///< Target commit
		std::vector< std::string > m_generatedPatches; ///< Generated patch files
	};

} // namespace migrate
} // namespace elomig

#endif // ELOMIG_PATCH_GENERATOR_H
