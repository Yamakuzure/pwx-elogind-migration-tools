/**
 * @file KindDetector.cpp
 * @brief Implementation of kind detection
 */

#include "KindDetector.h"

#include "utils/StringUtils.h"

#include <regex>

namespace elomig {
namespace reversion {

	ChangeKind KindDetector::detectKind( std::string const& text ) {
		ChangeKind kind = KIND_NONE;

		// Check for elogind (case-insensitive)
		if ( isElogind( text ) ) {
			kind = static_cast< ChangeKind >( kind | KIND_ELOGIND );
		}

		// Check for loginctl
		if ( isLoginctl( text ) ) {
			kind = static_cast< ChangeKind >( kind | KIND_LOGINCTL );
		}

		// Check for systemctl
		if ( isSystemctl( text ) ) {
			kind = static_cast< ChangeKind >( kind | KIND_SYSTEMCTL );
		}

		// Check for systemd
		if ( isSystemd( text ) ) {
			kind = static_cast< ChangeKind >( kind | KIND_SYSTEMD );
		}

		// Check for sleep.conf
		if ( isSleep( text ) ) {
			kind = static_cast< ChangeKind >( kind | KIND_SLEEP );
		}

		return kind;
	}

	bool KindDetector::isElogind( std::string const& text ) {
		// Match "elogind" but not "systemd-logind"
		static std::regex const elogindRegex( R"(\blogind\b)", std::regex_constants::icase );

		// Exclude if it's part of "systemd-logind"
		static std::regex const systemdLogindRegex( R"(systemd[-_]logind)", std::regex_constants::icase );

		if ( std::regex_search( text, systemdLogindRegex ) ) {
			return false;
		}

		return std::regex_search( text, elogindRegex );
	}

	bool KindDetector::isLoginctl( std::string const& text ) {
		static std::regex const loginctlRegex( R"(\bloginctl\b)", std::regex_constants::icase );
		return std::regex_search( text, loginctlRegex );
	}

	bool KindDetector::isSystemctl( std::string const& text ) {
		static std::regex const systemctlRegex( R"(\bsystemctl\b)", std::regex_constants::icase );
		return std::regex_search( text, systemctlRegex );
	}

	bool KindDetector::isSystemd( std::string const& text ) {
		// Match "systemd" in various contexts
		static std::regex const systemdRegex( R"(\bsystemd\b)", std::regex_constants::icase );

		return std::regex_search( text, systemdRegex );
	}

	bool KindDetector::isSleep( std::string const& text ) {
		// Match sleep.conf (with or without systemd- prefix)
		static std::regex const sleepRegex( R"((?:systemd[-_])?sleep\.conf)", std::regex_constants::icase );
		return std::regex_search( text, sleepRegex );
	}

	ChangeKind KindDetector::getPartnerKind( ChangeKind kind ) {
		switch ( kind ) {
			case KIND_ELOGIND:
				return KIND_SYSTEMD;

			case KIND_SYSTEMD:
				return KIND_ELOGIND;

			case KIND_LOGINCTL:
				return KIND_SYSTEMCTL;

			case KIND_SYSTEMCTL:
				return KIND_LOGINCTL;

			case KIND_SLEEP:
				// sleep.conf in elogind is systemd-sleep.conf in systemd
				return KIND_SYSTEMD;

			default:
				return KIND_NONE;
		}
	}

	bool KindDetector::hasPartner( ChangeKind kind ) {
		return ( kind & ( KIND_ELOGIND | KIND_SYSTEMD | KIND_LOGINCTL | KIND_SYSTEMCTL ) ) != 0;
	}

	std::string KindDetector::kindToString( ChangeKind kind ) {
		std::string result;

		if ( kind & KIND_ELOGIND ) {
			result += "elogind ";
		}
		if ( kind & KIND_LOGINCTL ) {
			result += "loginctl ";
		}
		if ( kind & KIND_SYSTEMCTL ) {
			result += "systemctl ";
		}
		if ( kind & KIND_SYSTEMD ) {
			result += "systemd ";
		}
		if ( kind & KIND_SLEEP ) {
			result += "sleep ";
		}

		if ( result.empty() ) {
			result = "none";
		} else if ( !result.empty() && result.back() == ' ' ) {
			result.pop_back();
		}

		return result;
	}

	bool KindDetector::matchesPattern( std::string const& text, std::string const& pattern ) {
		try {
			std::regex patternRegex( pattern, std::regex_constants::icase );
			return std::regex_search( text, patternRegex );
		} catch ( std::regex_error const& ) {
			// Fallback to simple substring search
			return utils::toLower( text ).find( utils::toLower( pattern ) ) != std::string::npos;
		}
	}

} // namespace reversion
} // namespace elomig
