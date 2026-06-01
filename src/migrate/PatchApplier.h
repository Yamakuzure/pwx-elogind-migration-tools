/**
 * @file PatchApplier.h
 * @brief Apply migrated patches to elogind repository
 *
 * Applies generated patches to the elogind repository with error handling
 * and recovery mechanisms.
 */

#ifndef ELOMIG_PATCH_APPLIER_H
#define ELOMIG_PATCH_APPLIER_H

#include "data/Patch.h"

#include <memory>
#include <string>
#include <vector>

namespace elomig {
namespace migrate {

	/**
	 * @brief Patch applier for elogind repository
	 *
	 * Applies patches to the local elogind repository with robust error handling
	 * and recovery mechanisms.
	 */
	class PatchApplier {
	public:
		/**
		 * @brief Default constructor
		 */
		PatchApplier();

		/**
		 * @brief Destructor
		 */
		~PatchApplier();

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
		 * @brief Apply a single patch
		 * @param patchFile Path to patch file
		 * @param continueOnFailure If true, continue applying patches despite errors
		 * @return True if successful
		 */
		bool applyPatch( std::string const& patchFile, bool continueOnFailure = false );

		/**
		 * @brief Apply a list of patches
		 * @param patchFiles Vector of patch file paths
		 * @param continueOnFailure If true, continue applying patches despite errors
		 * @return True if all patches applied successfully
		 */
		bool applyPatches( std::vector< std::string > const& patchFiles, bool continueOnFailure = false );

		/**
		 * @brief Apply patch with git am fallback
		 * @param patchFile Path to patch file
		 * @return True if successful
		 */
		bool applyPatchWithFallback( std::string const& patchFile );

		/**
		 * @brief Apply missing predecessors if needed
		 * @param patchFile Path to patch file
		 * @param patchesToApply Vector of patches to apply
		 * @return True if successful
		 */
		bool applyMissingPredecessors( std::string const& patchFile, std::vector< std::string > const& patchesToApply );

		/**
		 * @brief Get applied patches
		 * @return Vector of applied patch file paths
		 */
		std::vector< std::string > const& appliedPatches() const { return m_appliedPatches; }

		/**
		 * @brief Check if patch was already applied
		 * @param patchFile Path to patch file
		 * @return True if already applied
		 */
		bool isPatchApplied( std::string const& patchFile ) const;

	private:
		/**
		 * @brief Apply patch using git am
		 * @param patchFile Path to patch file
		 * @return True if successful
		 */
		bool applyGitAm( std::string const& patchFile );

		/**
		 * @brief Apply patch using manual patch command
		 * @param patchFile Path to patch file
		 * @return True if successful
		 */
		bool applyManualPatch( std::string const& patchFile );

		/**
		 * @brief Get patch commit hash from patch file
		 * @param patchFile Path to patch file
		 * @return Commit hash or empty string if not found
		 */
		std::string                getPatchCommitHash( std::string const& patchFile ) const;

		std::string                m_elogindPath;     ///< Elogind repository path
		std::string                m_upstreamPath;    ///< Upstream repository path
		std::vector< std::string > m_appliedPatches;  ///< Successfully applied patches
		std::set< std::string >    m_appliedPatchSet; ///< Set of applied patches for quick lookup
	};

} // namespace migrate
} // namespace elomig

#endif // ELOMIG_PATCH_APPLIER_H
