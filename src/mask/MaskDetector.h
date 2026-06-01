/**
 * @file MaskDetector.h
 * @brief Detect mask blocks in source files
 *
 * Identifies elogind mask blocks (#if 0 // elogind, #else // 0, #endif // 0)
 * and insert blocks (#if 1 // elogind) in various file types.
 */

#ifndef ELOMIG_MASK_DETECTOR_H
#define ELOMIG_MASK_DETECTOR_H

#include <memory>
#include <string>
#include <vector>

namespace elomig {
namespace mask {

	/**
	 * @brief Type of mask block
	 */
	enum class MaskType {
		NONE = 0,     ///< Not a mask block
		MASK_START,   ///< #if 0 // elogind
		MASK_ELSE,    ///< #else // 0
		MASK_END,     ///< #endif // 0
		INSERT_START, ///< #if 1 // elogind
		INSERT_END    ///< #endif // 1
	};

	/**
	 * @brief Represents a single mask block line
	 */
	struct MaskLine {
		MaskType    type;        ///< Type of mask directive
		int         lineNumber;  ///< Line number in file
		std::string content;     ///< Original line content
		bool        isCommented; ///< True if line is commented out (shell)
		int         nestLevel;   ///< Nesting level of mask

		MaskLine() : type( MaskType::NONE ), lineNumber( 0 ), isCommented( false ), nestLevel( 0 ) {}
	};

	/**
	 * @brief Mask block detector class
	 *
	 * Analyzes lines to detect mask blocks and tracks their state.
	 */
	class MaskDetector {
	public:
		/**
		 * @brief Default constructor
		 */
		MaskDetector();

		/**
		 * @brief Reset detector state
		 */
		void reset();

		/**
		 * @brief Check if a line is a mask directive
		 * @param line Line to check
		 * @param isShell True if line is from shell file
		 * @return Type of mask directive
		 */
		MaskType checkLine( std::string const& line, bool isShell = false ) const;

		/**
		 * @brief Process a line and update state
		 * @param line Line to process
		 * @param lineNumber Line number
		 * @param isShell True if from shell file
		 * @return MaskLine structure with detection results
		 */
		MaskLine processLine( std::string const& line, int lineNumber, bool isShell = false );

		/**
		 * @brief Get current mask nesting level
		 * @return Current nesting level
		 */
		int getNestLevel() const { return m_nestLevel; }

		/**
		 * @brief Check if currently inside a mask block
		 * @return True if inside mask
		 */
		bool isInMask() const { return m_inMask; }

		/**
		 * @brief Check if currently inside an insert block
		 * @return True if inside insert block
		 */
		bool isInInsert() const { return m_inInsert; }

		/**
		 * @brief Check if currently at #else of a mask
		 * @return True if at mask else
		 */
		bool isInMaskElse() const { return m_inMaskElse; }

		/**
		 * @brief Get mask type for a line (convenience)
		 * @param line Line to check
		 * @param isShell True if shell file
		 * @return MaskType enum value
		 */
		static MaskType getMaskType( std::string const& line, bool isShell = false );

		/**
		 * @brief Check if line matches mask start pattern
		 * @param line Line to check
		 * @return True if mask start
		 */
		static bool isMaskStart( std::string const& line, bool isShell = false );

		/**
		 * @brief Check if line matches mask else pattern
		 * @param line Line to check
		 * @return True if mask else
		 */
		static bool isMaskElse( std::string const& line, bool isShell = false );

		/**
		 * @brief Check if line matches mask end pattern
		 * @param line Line to check
		 * @return True if mask end
		 */
		static bool isMaskEnd( std::string const& line, bool isShell = false );

		/**
		 * @brief Check if line matches insert start pattern
		 * @param line Line to check
		 * @return True if insert start
		 */
		static bool isInsertStart( std::string const& line, bool isShell = false );

		/**
		 * @brief Check if line matches insert end pattern
		 * @param line Line to check
		 * @return True if insert end
		 */
		static bool isInsertEnd( std::string const& line, bool isShell = false );

	private:
		int  m_nestLevel;     ///< Current mask nesting level
		bool m_inMask;        ///< Inside mask block flag
		bool m_inInsert;      ///< Inside insert block flag
		bool m_inMaskElse;    ///< At #else of mask flag
		int  m_lastMaskLevel; ///< Level of last mask start
	};

} // namespace mask
} // namespace elomig

#endif // ELOMIG_MASK_DETECTOR_H
