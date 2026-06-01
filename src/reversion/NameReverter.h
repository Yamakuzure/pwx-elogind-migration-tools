/**
 * @file NameReverter.h
 * @brief Handle systemd↔elogind name reversions
 *
 * Detects pairs of changes where systemd names were changed to
 * elogind names (or vice versa) and reverts them appropriately.
 */

#ifndef ELOMIG_NAME_REVERTER_H
#define ELOMIG_NAME_REVERTER_H

#include "data/Hunk.h"
#include "reversion/KindDetector.h"

#include <map>
#include <memory>
#include <string>
#include <vector>

namespace elomig {

class Hunk;
class HunkLine;

namespace reversion {

	/**
	 * @brief Represents a single change (addition or removal)
	 */
	struct Change {
		int         lineIndex;    ///< Index in hunk
		LineType    type;         ///< ADDITION or REMOVAL
		std::string text;         ///< Line content (without prefix)
		std::string original;     ///< Original line with prefix
		ChangeKind  kind;         ///< What kind of reference
		std::string altText;      ///< Alternative text (reverted)
		bool        isComment;    ///< True if line is a comment
		bool        isMasked;     ///< True if inside mask block
		bool        done;         ///< True if change has been handled
		int         partnerIndex; ///< Index of partner change (-1 if none)
		int         prevIndex;    ///< Index of previous related change

		Change()
			: lineIndex( -1 )
			, type( LineType::CONTEXT )
			, kind( KIND_NONE )
			, isComment( false )
			, isMasked( false )
			, done( false )
			, partnerIndex( -1 )
			, prevIndex( -1 ) {}
	};

	/**
	 * @brief Change analysis results for a hunk
	 */
	struct ChangeAnalysis {
		std::map< int, std::shared_ptr< Change > >                        byLine; ///< Changes by line index
		std::map< std::string, std::vector< std::shared_ptr< Change > > > byText; ///< Changes by text

		void                                                              clear() {
			byLine.clear();
			byText.clear();
		}
	};

	/**
	 * @brief Name reverter for systemd↔elogind changes
	 *
	 * Analyzes hunks for name changes and reverts them appropriately.
	 */
	class NameReverter {
	public:
		/**
		 * @brief Default constructor
		 */
		NameReverter();

		/**
		 * @brief Process a hunk for name reversions
		 * @param hunk Hunk to process
		 * @param isShell True if hunk is from shell file
		 * @param isXML True if hunk is from XML file
		 * @return True if hunk was modified
		 */
		bool processHunk( std::shared_ptr< Hunk > hunk, bool isShell = false, bool isXML = false );

		/**
		 * @brief Analyze hunk for changes
		 * @param hunk Hunk to analyze
		 * @param analysis Output analysis results
		 * @return True if analysis found changes
		 */
		bool analyzeHunk( std::shared_ptr< Hunk > hunk, ChangeAnalysis& analysis );

		/**
		 * @brief Find and set partners for changes
		 * @param analysis Change analysis results
		 * @return Number of partnerships found
		 */
		int findPartners( ChangeAnalysis& analysis );

		/**
		 * @brief Handle solo changes (without partners)
		 * @param analysis Change analysis results
		 * @param hunk Hunk being processed
		 * @return True if modifications were made
		 */
		bool handleSoloChanges( ChangeAnalysis const& analysis, std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Handle partnered changes
		 * @param analysis Change analysis results
		 * @param hunk Hunk being processed
		 * @return True if modifications were made
		 */
		bool handlePartneredChanges( ChangeAnalysis const& analysis, std::shared_ptr< Hunk > hunk );

		/**
		 * @brief Find alternative text for a change
		 * @param text Original text
		 * @param kind Kind of reference
		 * @return Alternative text (empty if no alternative)
		 */
		static std::string findAltText( std::string const& text, ChangeKind kind );

		/**
		 * @brief Check if text is protected (should not be changed)
		 * @param text Text to check
		 * @param isComment True if text is in a comment
		 * @return True if text is protected
		 */
		static bool isProtectedText( std::string const& text, bool isComment );

		/**
		 * @brief Check if text is systemd-only content
		 * @param text Text to check
		 * @return True if text is systemd-specific
		 */
		static bool isSystemdOnly( std::string const& text );

		/**
		 * @brief Revert a name change
		 * @param text Original text
		 * @param kind Kind of change
		 * @return Reverted text
		 */
		static std::string revertName( std::string const& text, ChangeKind kind );

	private:
		/**
		 * @brief Analyze a single line for changes
		 * @param line Hunk line to analyze
		 * @param lineIndex Index of line
		 * @param isMasked True if line is in mask
		 * @param change Output change structure
		 * @return True if line contains a change
		 */
		bool analyzeLine( HunkLine const& line, int lineIndex, bool isMasked, Change& change );

		/**
		 * @brief Check if line is a comment
		 * @param line Hunk line
		 * @param isShell True if from shell file
		 * @return True if line is a comment
		 */
		bool isCommentLine( HunkLine const& line, bool isShell ) const;

		/**
		 * @brief Check if change should be spliced out
		 * @param change Change to check
		 * @return True if change should be spliced
		 */
		bool shouldSplice( Change const& change ) const;

		bool m_debugMode; ///< Debug mode flag
	};

} // namespace reversion
} // namespace elomig

#endif // ELOMIG_NAME_REVERTER_H
