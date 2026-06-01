/**
 * @file MaskHandler.h
 * @brief Handle mask blocks in hunks
 *
 * Processes hunks to properly handle elogind mask blocks,
 * ensuring protected code is not accidentally modified.
 */

#ifndef ELOMIG_MASK_HANDLER_H
#define ELOMIG_MASK_HANDLER_H

#include "mask/MaskDetector.h"

#include <memory>
#include <vector>

namespace elomig {

class Hunk;
class FileDiff;

namespace mask {

	/**
	 * @brief Mask block handler for hunks
	 *
	 * Analyzes hunks for mask blocks and applies transformations
	 * to protect elogind-specific code.
	 */
	class MaskHandler {
	public:
		/**
		 * @brief Default constructor
		 */
		MaskHandler();

		/**
		 * @brief Process a hunk for mask blocks
		 * @param hunk Hunk to process
		 * @param fileDiff Parent file diff
		 * @return True if hunk was modified
		 */
		bool processHunk( std::shared_ptr< Hunk > hunk, std::shared_ptr< FileDiff > fileDiff );

		/**
		 * @brief Check if hunk has valid mask structure
		 * @param hunk Hunk to check
		 * @return True if masks are well-formed
		 */
		bool checkMaskStructure( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Sanitize mask blocks in hunk
		 * @param hunk Hunk to sanitize
		 * @return Number of fixes applied
		 */
		int sanitizeMasks( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Handle removals inside mask blocks
		 * @param hunk Hunk to process
		 * @return True if modifications were made
		 */
		bool handleMaskRemovals( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Handle additions after mask blocks
		 * @param hunk Hunk to process
		 * @return True if modifications were made
		 */
		bool handleMaskAdditions( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Convert empty mask to comment
		 * @param hunk Hunk to process
		 * @return True if mask was converted
		 */
		bool convertEmptyMask( std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Get current mask state
		 * @return Current mask detector state
		 */
		MaskDetector const& detector() const { return m_detector; }

		/**
		 * @brief Reset handler state
		 */
		void reset() { m_detector.reset(); }

	private:
		/**
		 * @brief Check if line is inside mask block
		 * @param lineIndex Index of line in hunk
		 * @return True if inside mask
		 */
		bool isLineInMask( size_t lineIndex ) const;

		/**
		 * @brief Get mask level at line
		 * @param lineIndex Index of line
		 * @return Mask nesting level
		 */
		int getMaskLevelAt( size_t lineIndex ) const;

		/**
		 * @brief Find matching #endif for a #if
		 * @param startIndex Index of #if line
		 * @return Index of matching #endif, or -1
		 */
		int                     findMatchingEndif( size_t startIndex ) const;

		MaskDetector            m_detector;   ///< Mask state detector
		std::vector< MaskLine > m_maskLines;  ///< Detected mask lines
		std::vector< bool >     m_inMask;     ///< Per-line mask state
		std::vector< int >      m_maskLevels; ///< Per-line mask level
	};

} // namespace mask
} // namespace elomig

#endif // ELOMIG_MASK_HANDLER_H
