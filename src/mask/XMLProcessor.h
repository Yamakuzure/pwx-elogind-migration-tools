/**
 * @file XMLProcessor.h
 * @brief Process XML files for mask block handling
 *
 * Handles preparation and unpreparation of XML files,
 * where mask blocks need special handling for entities
 * and comments.
 */

#ifndef ELOMIG_XML_PROCESSOR_H
#define ELOMIG_XML_PROCESSOR_H

#include <memory>
#include <string>
#include <vector>

namespace elomig {

class FileDiff;

namespace mask {

	/**
	 * @brief XML file mask processor
	 *
	 * Manages mask blocks in XML files, including handling of
	 * &#x2D; entities (dash) in mask comments.
	 */
	class XMLProcessor {
	public:
		/**
		 * @brief Default constructor
		 */
		XMLProcessor();

		/**
		 * @brief Prepare an XML file for diffing
		 *
		 * Handles mask blocks and restores &#x2D; entities.
		 *
		 * @param sourcePath Source file path
		 * @param tempPath Output temporary file path
		 * @return True if preparation succeeded
		 */
		bool prepare( std::string const& sourcePath, std::string& tempPath );

		/**
		 * @brief Unprepare an XML file after diffing
		 *
		 * Restores original entity encoding.
		 *
		 * @param tempPath Temporary file path
		 * @param originalPath Original file path
		 * @return True if unpreparation succeeded
		 */
		bool unprepare( std::string const& tempPath, std::string const& originalPath );

		/**
		 * @brief Prepare XML content in memory
		 * @param lines Input lines
		 * @param preparedLines Output prepared lines
		 * @return True if preparation succeeded
		 */
		bool prepareContent( std::vector< std::string > const& lines, std::vector< std::string >& preparedLines );

		/**
		 * @brief Unprepare XML content in memory
		 * @param preparedLines Prepared lines
		 * @param originalLines Output original lines
		 * @return True if unpreparation succeeded
		 */
		bool unprepareContent( std::vector< std::string > const& preparedLines, std::vector< std::string >& originalLines );

		/**
		 * @brief Check if a file needs XML preparation
		 * @param filePath File path to check
		 * @return True if file is XML needing preparation
		 */
		static bool needsPreparation( std::string const& filePath );

		/**
		 * @brief Apply mask block wrapping to XML content
		 * @param content XML content
		 * @param maskStart Mask start marker
		 * @param maskEnd Mask end marker
		 * @return Wrapped content
		 */
		static std::string wrapWithMask( std::string const& content, std::string const& maskStart, std::string const& maskEnd );

	private:
		/**
		 * @brief Restore &#x2D; entities to dashes in mask blocks
		 * @param line Line to process
		 * @param inMask True if currently in mask block
		 * @return Processed line
		 */
		std::string restoreDashEntities( std::string const& line, bool inMask );

		/**
		 * @brief Check if line contains XML comment with mask
		 * @param line Line to check
		 * @return True if line has XML mask comment
		 */
		bool isXMLMaskComment( std::string const& line ) const;

		/**
		 * @brief Check if line starts an XML mask block
		 * @param line Line to check
		 * @return True if line starts XML mask
		 */
		bool isXMLMaskStart( std::string const& line ) const;

		/**
		 * @brief Check if line ends an XML mask block
		 * @param line Line to check
		 * @return True if line ends XML mask
		 */
		bool                                         isXMLMaskEnd( std::string const& line ) const;

		bool                                         m_inMask;           ///< Current mask state
		std::vector< std::pair< int, std::string > > m_originalEntities; ///< Saved entities
	};

} // namespace mask
} // namespace elomig

#endif // ELOMIG_XML_PROCESSOR_H
