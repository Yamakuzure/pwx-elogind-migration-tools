/**
 * @file HunkRefactorer.h
 * @brief Main hunk refactoring orchestrator
 *
 * Coordinates all hunk transformation passes.
 */

#ifndef ELOMIG_HUNK_REFACTORER_H
#define ELOMIG_HUNK_REFACTORER_H

#include <memory>
#include <vector>

namespace elomig {

class Hunk;
class FileDiff;

namespace reversion {
	class NameReverter;
}

namespace include {
	class IncludeReconciler;
}

/**
 * @brief Orchestrates hunk refactoring passes
 */
class HunkRefactorer {
public:
	HunkRefactorer();
	~HunkRefactorer();

	/**
	 * @brief Process a single hunk through all passes
	 * @param hunk Hunk to process
	 * @param fileDiff Parent file diff
	 */
	void processHunk( std::shared_ptr< Hunk > hunk, std::shared_ptr< FileDiff > fileDiff );

	/**
	 * @brief Finalize all hunks
	 * @param fileDiff File diff to finalize
	 */
	void finishHunks( std::shared_ptr< FileDiff > fileDiff );

	/**
	 * @brief Check hunk sanity
	 * @param hunk Hunk to check
	 * @return True if hunk is valid
	 */
	bool checkHunkSanity( std::shared_ptr< Hunk > hunk );

private:
	// Refactoring passes
	void                                          checkMasks( std::shared_ptr< Hunk > hunk, std::shared_ptr< FileDiff > fileDiff );
	void                                          checkMusl( std::shared_ptr< Hunk > hunk );
	void                                          checkDebug( std::shared_ptr< Hunk > hunk );
	void                                          checkNameReverts( std::shared_ptr< Hunk > hunk );
	void                                          checkUseless( std::shared_ptr< Hunk > hunk );
	void                                          checkEmptyMasks( std::shared_ptr< Hunk > hunk );
	void                                          checkIncludes( std::shared_ptr< Hunk > hunk );
	void                                          checkComments( std::shared_ptr< Hunk > hunk );
	void                                          checkFunctions( std::shared_ptr< Hunk > hunk );

	bool                                          m_debugMode;
	std::unique_ptr< reversion::NameReverter >    m_nameReverter;      ///< Name reverter instance
	std::unique_ptr< include::IncludeReconciler > m_includeReconciler; ///< Include reconciler instance
};

} // namespace elomig

#endif // ELOMIG_HUNK_REFACTORER_H
