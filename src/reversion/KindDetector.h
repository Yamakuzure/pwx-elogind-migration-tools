/**
 * @file KindDetector.h
 * @brief Detect the kind of systemd/elogind reference
 *
 * Identifies whether a line refers to elogind, systemd, loginctl,
 * systemctl, or sleep-related components.
 */

#ifndef ELOMIG_KIND_DETECTOR_H
#define ELOMIG_KIND_DETECTOR_H

#include <cstdint>
#include <string>

namespace elomig {
namespace reversion {

	/**
	 * @brief Bit flags for change kinds
	 */
	enum ChangeKind : uint8_t {
		KIND_NONE      = 0,
		KIND_ELOGIND   = 1 << 0, ///< Refers to elogind
		KIND_LOGINCTL  = 1 << 1, ///< Refers to loginctl
		KIND_SYSTEMCTL = 1 << 2, ///< Refers to systemctl
		KIND_SYSTEMD   = 1 << 3, ///< Refers to systemd
		KIND_SLEEP     = 1 << 4  ///< Refers to sleep.conf
	};

	/**
	 * @brief Detector for change kinds
	 *
	 * Analyzes text to determine what kind of systemd/elogind
	 * component it references.
	 */
	class KindDetector {
	public:
		/**
		 * @brief Default constructor
		 */
		KindDetector() = default;

		/**
		 * @brief Detect the kind of reference in text
		 * @param text Text to analyze
		 * @return ChangeKind bit flags
		 */
		static ChangeKind detectKind( std::string const& text );

		/**
		 * @brief Check if text contains elogind reference
		 * @param text Text to check
		 * @return True if contains elogind
		 */
		static bool isElogind( std::string const& text );

		/**
		 * @brief Check if text contains loginctl reference
		 * @param text Text to check
		 * @return True if contains loginctl
		 */
		static bool isLoginctl( std::string const& text );

		/**
		 * @brief Check if text contains systemctl reference
		 * @param text Text to check
		 * @return True if contains systemctl
		 */
		static bool isSystemctl( std::string const& text );

		/**
		 * @brief Check if text contains systemd reference
		 * @param text Text to check
		 * @return True if contains systemd
		 */
		static bool isSystemd( std::string const& text );

		/**
		 * @brief Check if text contains sleep.conf reference
		 * @param text Text to check
		 * @return True if contains sleep.conf
		 */
		static bool isSleep( std::string const& text );

		/**
		 * @brief Get the partner kind for a given kind
		 * @param kind Original kind
		 * @return Partner kind (systemd<->elogind, systemctl<->loginctl)
		 */
		static ChangeKind getPartnerKind( ChangeKind kind );

		/**
		 * @brief Check if kind has a partner
		 * @param kind Kind to check
		 * @return True if kind has a partner
		 */
		static bool hasPartner( ChangeKind kind );

		/**
		 * @brief Convert kind to string
		 * @param kind Kind to convert
		 * @return String representation
		 */
		static std::string kindToString( ChangeKind kind );

	private:
		/**
		 * @brief Check if text matches a pattern (case-insensitive)
		 * @param text Text to check
		 * @param pattern Pattern to match
		 * @return True if pattern found
		 */
		static bool matchesPattern( std::string const& text, std::string const& pattern );
	};

} // namespace reversion
} // namespace elomig

#endif // ELOMIG_KIND_DETECTOR_H
