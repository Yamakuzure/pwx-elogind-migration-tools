/**
 * @file IncludeReconciler.h
 * @brief Reconcile include directive changes and resolve conflicts
 *
 * Handles the reconciliation of include directives, resolving conflicts
 * and ensuring elogind-specific includes are properly maintained.
 */

#ifndef ELOMIG_INCLUDE_RECONCILER_H
#define ELOMIG_INCLUDE_RECONCILER_H

#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

namespace elomig {

class Hunk;
class FileDiff;

namespace include {

	/**
	 * @brief Include reconciliation manager
	 *
	 * Manages include directive reconciliation and conflict resolution
	 * across multiple hunks in a file diff.
	 */
	class IncludeReconciler {
	public:
		/**
		 * @brief Default constructor
		 */
		IncludeReconciler();

		/**
		 * @brief Process a hunk for include reconciliations
		 * @param hunk Hunk to process
		 * @param fileDiff Parent file diff
		 * @return True if hunk was modified
		 */
		bool processHunk( std::shared_ptr< Hunk > hunk, std::shared_ptr< FileDiff > fileDiff );

		/**
		 * @brief Process all hunks in a file diff for include reconciliation
		 * @param fileDiff File diff to process
		 * @return True if any changes were made
		 */
		bool processFile( std::shared_ptr< FileDiff > fileDiff );

		/**
		 * @brief Check for include conflicts
		 * @param hunk Hunk to check
		 * @return True if conflicts found
		 */
		bool checkConflicts( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Resolve include conflicts
		 * @param hunk Hunk with conflicts
		 * @return True if conflicts were resolved
		 */
		bool resolveConflicts( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Handle include additions/removals
		 * @param hunk Hunk to process
		 * @return True if changes were made
		 */
		bool handleIncludeChanges( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Check if include should be protected
		 * @param fileName Include file name
		 * @return True if include should be protected
		 */
		static bool shouldProtectInclude( std::string const& fileName );

		/**
		 * @brief Check if include removal should be reverted
		 * @param fileName Include file name
		 * @param isRemoved True if removal was attempted
		 * @return True if removal should be reverted
		 */
		static bool shouldRevertRemoval( std::string const& fileName, bool isRemoved );

		/**
		 * @brief Get elogind-specific include patterns
		 * @return Vector of patterns
		 */
		static std::vector< std::string > const& getElogindIncludePatterns();

	private:
		/**
		 * @brief Track include changes across hunks
		 * @param hunk Hunk to analyze
		 */
		void trackIncludeChanges( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Splice out unwanted include additions
		 * @param hunk Hunk to process
		 * @return True if splicing occurred
		 */
		bool spliceUnwantedIncludes( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Protect elogind-specific includes from removal
		 * @param hunk Hunk to process
		 * @return True if protection occurred
		 */
		bool                                     protectElogindIncludes( std::shared_ptr< Hunk > hunk );

		std::map< std::string, std::set< int > > m_includeHunks;    ///< Map of includes to hunks
		std::map< std::string, bool >            m_removedIncludes; ///< Track removed includes
		std::map< std::string, bool >            m_addedIncludes;   ///< Track added includes
		std::set< std::string >                  m_elogindIncludes; ///< Elogind-specific includes
	};

} // namespace include
} // namespace elomig

#endif // ELOMIG_INCLUDE_RECONCILER_H
