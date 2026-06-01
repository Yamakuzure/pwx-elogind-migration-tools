/**
 * @file CommitFile.cpp
 * @brief Implementation of commit file handling
 */

#include "CommitFile.h"

#include "utils/FileUtil.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <algorithm>
#include <fstream>
#include <sstream>

namespace elomig {
namespace migrate {

	CommitFile::CommitFile() : m_commitsRead( false ) {}

	CommitFile::~CommitFile() {
		// Write changes if needed
		if ( m_commitsRead ) {
			writeMutualCommits();
		}
	}

	bool CommitFile::readMutualCommits() {
		LOG_DEBUG( "Reading mutual commits from %s", m_filePath.c_str() );

		if ( m_filePath.empty() ) {
			LOG_ERROR( "No CSV file path specified" );
			return false;
		}

		m_mutualCommits.clear();

		if ( !utils::fileExists( m_filePath ) ) {
			LOG_DEBUG( "CSV file does not exist, creating empty" );
			return true;
		}

		std::vector< std::string > lines;
		if ( !utils::readFile( m_filePath, lines ) ) {
			LOG_ERROR( "Failed to read CSV file: %s", m_filePath.c_str() );
			return false;
		}

		for ( auto const& line : lines ) {
			// Skip empty and comment lines
			std::string trimmed = utils::trim( line );
			if ( trimmed.empty() || trimmed[0] == '#' ) {
				continue;
			}

			MutualCommitEntry entry = parseCsvLine( trimmed );
			if ( !entry.upstreamPath.empty() ) {
				// Create key for map
				std::string key      = entry.upstreamPath + ":" + entry.refId;
				m_mutualCommits[key] = entry;
			}
		}

		m_commitsRead = true;
		LOG_DEBUG( "Loaded %zu mutual commit entries", m_mutualCommits.size() );
		return true;
	}

	bool CommitFile::writeMutualCommits() {
		LOG_DEBUG( "Writing mutual commits to %s", m_filePath.c_str() );

		if ( m_filePath.empty() ) {
			LOG_ERROR( "No CSV file path specified" );
			return false;
		}

		std::vector< std::string > lines;

		// Add header
		lines.push_back( "# Automatically generated commit information" );
		lines.push_back( "# Only edit if you know what these do!" );
		lines.push_back( "" );

		// Add entries
		for ( auto const& pair : m_mutualCommits ) {
			lines.push_back( formatCsvLine( pair.second ) );
		}

		// Write to file
		if ( !utils::writeFile( m_filePath, lines ) ) {
			LOG_ERROR( "Failed to write CSV file: %s", m_filePath.c_str() );
			return false;
		}

		LOG_DEBUG( "Successfully wrote %zu mutual commit entries", m_mutualCommits.size() );
		return true;
	}

	MutualCommitEntry CommitFile::getMutualCommit( std::string const& upstreamPath, std::string const& refId ) const {
		std::string key = upstreamPath + ":" + refId;
		auto        it  = m_mutualCommits.find( key );
		if ( it != m_mutualCommits.end() ) {
			return it->second;
		}

		return MutualCommitEntry();
	}

	void CommitFile::setMutualCommit( std::string const& upstreamPath, std::string const& refId, MutualCommitEntry const& entry ) {
		std::string key      = upstreamPath + ":" + refId;
		m_mutualCommits[key] = entry;
	}

	bool CommitFile::updateMutualCommit(
		std::string const& upstreamPath,
		std::string const& refId,
		std::string const& mutualHash,
		std::string const& srcHash,
		std::string const& tgtHash
	) {
		MutualCommitEntry entry( upstreamPath, refId );
		entry.mutual = mutualHash;
		entry.src    = srcHash;
		entry.tgt    = tgtHash;

		setMutualCommit( upstreamPath, refId, entry );
		return true;
	}

	MutualCommitEntry CommitFile::parseCsvLine( std::string const& line ) const {
		MutualCommitEntry          entry;

		std::vector< std::string > parts = utils::split( line, '\t' );

		if ( parts.size() >= 5 ) {
			entry.upstreamPath = utils::trim( parts[0] );
			entry.refId        = utils::trim( parts[1] );
			entry.mutual       = utils::trim( parts[2] );
			entry.src          = utils::trim( parts[3] );
			entry.tgt          = utils::trim( parts[4] );
		}

		return entry;
	}

	std::string CommitFile::formatCsvLine( MutualCommitEntry const& entry ) const {
		std::string src = entry.src.empty() ? "x" : entry.src;
		std::string tgt = entry.tgt.empty() ? "x" : entry.tgt;

		// Ensure src and tgt are properly formatted for CSV
		if ( src.length() > 4 ) {
			src = "src-" + src;
		}
		if ( tgt.length() > 4 ) {
			tgt = "tgt-" + tgt;
		}

		return entry.upstreamPath + "\t" + entry.refId + "\t" + entry.mutual + "\t" + src + "\t" + tgt;
	}

} // namespace migrate
} // namespace elomig
