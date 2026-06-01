/**
 * @file NameReverter.cpp
 * @brief Implementation of name reversion logic
 */

#include "NameReverter.h"

#include "data/Hunk.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

namespace elomig {
namespace reversion {

	NameReverter::NameReverter() : m_debugMode( false ) {}

	bool NameReverter::processHunk( std::shared_ptr< Hunk > hunk, bool isShell, bool isXML ) {
		if ( !hunk || !hunk->isUseful() ) {
			return false;
		}

		LOG_DEBUG( "Processing name reversions in hunk %d", hunk->index() );

		ChangeAnalysis analysis;
		if ( !analyzeHunk( hunk, analysis ) ) {
			return false;
		}

		bool modified = false;

		// Find partners for changes
		int partnerships = findPartners( analysis );
		LOG_DEBUG( "Found %d partnerships in hunk %d", partnerships, hunk->index() );

		// Handle partnered changes first
		modified |= handlePartneredChanges( analysis, hunk );

		// Then handle solo changes
		modified |= handleSoloChanges( analysis, hunk );

		return modified;
	}

	bool NameReverter::analyzeHunk( std::shared_ptr< Hunk > hunk, ChangeAnalysis& analysis ) {
		analysis.clear();

		bool foundChanges = false;
		bool inMask       = false;

		for ( int i = 0; i < static_cast< int >( hunk->lineCount() ); ++i ) {
			auto const& line = hunk->lineAt( i );

			// Update mask state (simplified)
			std::string trimmed = utils::trim( line.original );
			if ( trimmed.find( "#if 0" ) != std::string::npos ) {
				inMask = true;
			} else if ( trimmed.find( "#endif" ) != std::string::npos ) {
				inMask = false;
			}

			// Only process additions and removals
			if ( line.type != LineType::ADDITION && line.type != LineType::REMOVAL ) {
				continue;
			}

			Change change;
			if ( analyzeLine( line, i, inMask, change ) ) {
				foundChanges       = true;

				auto changePtr     = std::make_shared< Change >( change );
				analysis.byLine[i] = changePtr;
				analysis.byText[change.text].push_back( changePtr );

				LOG_DEBUG(
					"Found %s change at line %d: kind=%s",
					line.type == LineType::ADDITION ? "ADDITION" : "REMOVAL",
					i,
					KindDetector::kindToString( change.kind ).c_str()
				);
			}
		}

		return foundChanges;
	}

	bool NameReverter::analyzeLine( HunkLine const& line, int lineIndex, bool isMasked, Change& change ) {
		change.lineIndex = lineIndex;
		change.type      = line.type;
		change.original  = line.original;
		change.isMasked  = isMasked;
		change.text      = line.content;

		// Check if line contains systemd/elogind references
		change.kind = KindDetector::detectKind( change.text );

		if ( change.kind == KIND_NONE ) {
			return false;
		}

		change.isComment = isCommentLine( line, false );
		change.altText   = findAltText( change.text, change.kind );

		return true;
	}

	bool NameReverter::isCommentLine( HunkLine const& line, bool isShell ) const {
		std::string trimmed = utils::trim( line.content );

		if ( isShell ) {
			return !trimmed.empty() && trimmed[0] == '#';
		} else {
			return utils::startsWith( trimmed, "//" ) || utils::startsWith( trimmed, "/*" ) || utils::startsWith( trimmed, "*" );
		}
	}

	int NameReverter::findPartners( ChangeAnalysis& analysis ) {
		int partnerships = 0;

		for ( auto& [lineIdx, changePtr] : analysis.byLine ) {
			if ( !changePtr || changePtr->done || changePtr->partnerIndex >= 0 ) {
				continue;
			}

			ChangeKind partnerKind = KindDetector::getPartnerKind( changePtr->kind );

			if ( !KindDetector::hasPartner( changePtr->kind ) ) {
				continue;
			}

			std::shared_ptr< Change > bestPartner;
			int                       bestDistance = INT32_MAX;

			for ( auto& [otherIdx, otherPtr] : analysis.byLine ) {
				if ( !otherPtr || otherPtr->done || otherPtr->partnerIndex >= 0 ) {
					continue;
				}

				if ( changePtr->type == otherPtr->type ) {
					continue;
				}

				if ( otherPtr->kind != partnerKind ) {
					continue;
				}

				bool textMatches = ( otherPtr->altText == changePtr->text ) || ( otherPtr->text == changePtr->altText );

				if ( !textMatches ) {
					continue;
				}

				int distance = std::abs( otherIdx - lineIdx );
				if ( distance < bestDistance ) {
					bestPartner  = otherPtr;
					bestDistance = distance;
				}
			}

			if ( bestPartner ) {
				changePtr->partnerIndex   = bestPartner->lineIndex;
				bestPartner->partnerIndex = lineIdx;
				partnerships++;

				LOG_DEBUG( "Partnership: line %d <-> line %d", lineIdx, bestPartner->lineIndex );
			}
		}

		return partnerships;
	}

	bool NameReverter::handleSoloChanges( ChangeAnalysis const& analysis, std::shared_ptr< Hunk > hunk ) {
		bool modified = false;

		for ( auto const& [lineIdx, changePtr] : analysis.byLine ) {
			if ( !changePtr || changePtr->done || changePtr->partnerIndex >= 0 ) {
				continue;
			}

			LOG_DEBUG( "Handling solo change at line %d", lineIdx );

			if ( changePtr->isMasked ) {
				hunk->lineAt( lineIdx ).done = true;
				modified                     = true;
				continue;
			}

			if ( isProtectedText( changePtr->text, changePtr->isComment ) ) {
				if ( changePtr->type == LineType::REMOVAL ) {
					auto& line    = hunk->lineAt( lineIdx );
					line.type     = LineType::CONTEXT;
					line.original = ' ' + line.content;
					line.done     = true;
					modified      = true;
				}
				continue;
			}

			if ( changePtr->type == LineType::ADDITION && isSystemdOnly( changePtr->text ) ) {
				LOG_DEBUG( "Splicing systemd-only addition at line %d", lineIdx );
				hunk->lineAt( lineIdx ).done = true;
				modified                     = true;
				continue;
			}

			if ( changePtr->type == LineType::ADDITION && !changePtr->altText.empty() ) {
				auto&       line     = hunk->lineAt( lineIdx );
				std::string reverted = revertName( line.content, changePtr->kind );
				if ( !reverted.empty() ) {
					line.content  = reverted;
					line.original = '+' + reverted;
					modified      = true;
					LOG_DEBUG( "Reverted name at line %d", lineIdx );
				}
			}

			if ( changePtr->type == LineType::REMOVAL && ( changePtr->kind & KIND_ELOGIND ) ) {
				auto& line    = hunk->lineAt( lineIdx );
				line.type     = LineType::CONTEXT;
				line.original = ' ' + line.content;
				line.done     = true;
				modified      = true;
				LOG_DEBUG( "Kept elogind removal at line %d", lineIdx );
			}
		}

		return modified;
	}

	bool NameReverter::handlePartneredChanges( ChangeAnalysis const& analysis, std::shared_ptr< Hunk > hunk ) {
		bool modified = false;

		for ( auto const& [lineIdx, changePtr] : analysis.byLine ) {
			if ( !changePtr || changePtr->done || changePtr->partnerIndex < 0 ) {
				continue;
			}

			auto partnerIt = analysis.byLine.find( changePtr->partnerIndex );
			if ( partnerIt == analysis.byLine.end() ) {
				continue;
			}

			LOG_DEBUG( "Handling partnered changes: %d <-> %d", lineIdx, changePtr->partnerIndex );

			auto& line           = hunk->lineAt( lineIdx );
			line.type            = LineType::CONTEXT;
			line.original        = ' ' + line.content;
			line.done            = true;
			modified             = true;

			auto& partnerLine    = hunk->lineAt( changePtr->partnerIndex );
			partnerLine.type     = LineType::CONTEXT;
			partnerLine.original = ' ' + partnerLine.content;
			partnerLine.done     = true;
			modified             = true;
		}

		return modified;
	}

	std::string NameReverter::findAltText( std::string const& text, ChangeKind kind ) {
		return revertName( text, kind );
	}

	bool NameReverter::isProtectedText( std::string const& text, bool isComment ) {
		static std::vector< std::string > const protectedPatterns = {
			"systemd --user", "systemd-logind", "systemd-stable", "freedesktop.org/software/systemd", "fedoraproject.org/projects/systemd", "systemd.io"
		};

		std::string lowerText = utils::toLower( text );

		for ( auto const& pattern : protectedPatterns ) {
			if ( lowerText.find( utils::toLower( pattern ) ) != std::string::npos ) {
				return true;
			}
		}

		if ( isComment && lowerText.find( "systemd user" ) != std::string::npos ) {
			return true;
		}

		return false;
	}

	bool NameReverter::isSystemdOnly( std::string const& text ) {
		static std::vector< std::string > const systemdOnlyPatterns = {
			"systemd-homed",
			"systemd-resolved",
			"systemd-networkd",
			"systemd-timesyncd",
			"systemd-journal",
			"systemd-coredump",
			"systemd-oomd",
			"systemd-sysusers",
			"systemd-tmpfiles",
			"systemd-machine-id",
			"-Dcompat-mutable-uid-boundaries",
			"systemd-man",
			"systemd.service"
		};

		std::string lowerText = utils::toLower( text );

		for ( auto const& pattern : systemdOnlyPatterns ) {
			if ( lowerText.find( pattern ) != std::string::npos ) {
				return true;
			}
		}

		if ( text.find( "freedesktop.org/software/systemd/man" ) != std::string::npos ) {
			return true;
		}

		return false;
	}

	std::string NameReverter::revertName( std::string const& text, ChangeKind kind ) {
		std::string result = text;

		switch ( kind ) {
			case KIND_ELOGIND:
				result = utils::replaceAll( result, "elogind", "systemd" );
				result = utils::replaceAll( result, "ELOGIND", "SYSTEMD" );
				result = utils::replaceAll( result, "sleep.conf", "systemd-sleep.conf" );
				break;

			case KIND_SYSTEMD:
				result = utils::replaceAll( result, "systemd-logind", "elogind" );
				result = utils::replaceAll( result, "systemd-stable", "elogind" );
				result = utils::replaceAll( result, "systemd-userdbd.service", "elogind-userdbd" );
				result = utils::replaceAll( result, "systemd-sleep.conf", "sleep.conf" );
				result = utils::replaceAll( result, "systemd.io", "github.com/elogind/elogind" );

				if ( result.find( "systemd" ) != std::string::npos && result.find( "elogind" ) == std::string::npos ) {
					result = utils::replaceAll( result, "systemd", "elogind" );
				}
				break;

			case KIND_LOGINCTL:
				result = utils::replaceAll( result, "loginctl", "systemctl" );
				result = utils::replaceAll( result, "LOGINCTL", "SYSTEMCTL" );
				break;

			case KIND_SYSTEMCTL:
				result = utils::replaceAll( result, "systemctl", "loginctl" );
				result = utils::replaceAll( result, "SYSTEMCTL", "LOGINCTL" );
				break;

			default:
				break;
		}

		if ( kind & ( KIND_SYSTEMD | KIND_ELOGIND ) ) {
			if ( result.find( "<manvolnum>1</manvolnum>" ) != std::string::npos ) {
				result = utils::replaceAll( result, "<manvolnum>1</manvolnum>", "<manvolnum>8</manvolnum>" );
			} else if ( result.find( "<manvolnum>8</manvolnum>" ) != std::string::npos ) {
				result = utils::replaceAll( result, "<manvolnum>8</manvolnum>", "<manvolnum>1</manvolnum>" );
			}
		}

		if ( result.find( "elogind_headers" ) != std::string::npos ) {
			result = utils::replaceAll( result, "elogind_headers", "systemd_headers" );
		}

		return ( result != text ) ? result : "";
	}

	bool NameReverter::shouldSplice( Change const& change ) const {
		if ( change.type == LineType::ADDITION && isSystemdOnly( change.text ) ) {
			return true;
		}

		return false;
	}

} // namespace reversion
} // namespace elomig
