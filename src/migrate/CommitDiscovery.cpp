/**
 * @file CommitDiscovery.cpp
 * @brief Implementation of commit discovery
 */

#include "CommitDiscovery.h"

#include "utils/FileUtil.h"
#include "utils/GitWrapper.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <algorithm>
#include <set>

namespace elomig {
namespace migrate {

	CommitDiscovery::CommitDiscovery() {}

	CommitDiscovery::~CommitDiscovery() {}

	bool CommitDiscovery::discoverCommits() {
		LOG_DEBUG( "Discovering commits for migration" );

		if ( m_upstreamPath.empty() || m_targetRef.empty() ) {
			LOG_ERROR( "Missing upstream path or target reference" );
			return false;
		}

		GitWrapper git( m_upstreamPath );
		if ( !git.isValid() ) {
			LOG_ERROR( "Invalid upstream repository" );
			return false;
		}

		// Build file-to-commit mapping
		if ( !buildFileCommitMapping() ) {
			LOG_ERROR( "Failed to build file-commit mapping" );
			return false;
		}

		// Build chronological commit list
		if ( !buildCommitList() ) {
			LOG_ERROR( "Failed to build commit list" );
			return false;
		}

		LOG_DEBUG( "Discovered %zu relevant commits", m_commits.size() );
		return true;
	}

	bool CommitDiscovery::buildFileCommitMapping() {
		LOG_DEBUG( "Building file-commit mapping" );

		GitWrapper git( m_upstreamPath );
		if ( !git.isValid() ) {
			return false;
		}

		// For each source file, find commits that touch it
		for ( auto const& file : m_sourceFiles ) {
			std::string systemdFile = file;

			// Convert elogind path to systemd path
			systemdFile = utils::replaceAll( systemdFile, "elogind", "systemd" );

			LOG_DEBUG( "Finding commits affecting file: %s", systemdFile.c_str() );

			// Get commits touching this file
			auto commits = git.getFileCommits( m_mutualCommit, m_targetRef, systemdFile );
			LOG_DEBUG( "Found %zu commits for file %s", commits.size(), systemdFile.c_str() );

			// Add to file-to-commits mapping
			for ( auto const& commit : commits ) {
				m_fileCommits[systemdFile].insert( commit );
				m_relevantCommits.insert( commit );
			}
		}

		return true;
	}

	bool CommitDiscovery::buildCommitList() {
		LOG_DEBUG( "Building chronological commit list" );

		GitWrapper git( m_upstreamPath );
		if ( !git.isValid() ) {
			return false;
		}

		// Get all commits in chronological order
		m_commits = git.revList( m_mutualCommit, m_targetRef, "", true, true );

		// Filter to only commits that affect source files
		std::vector< std::string > filteredCommits;
		for ( auto const& commit : m_commits ) {
			if ( m_relevantCommits.find( commit ) != m_relevantCommits.end() ) {
				filteredCommits.push_back( commit );
			}
		}

		m_commits = filteredCommits;

		LOG_DEBUG( "Built commit list with %zu commits", m_commits.size() );
		return true;
	}

	MigrationCommitInfo CommitDiscovery::getCommitInfo( std::string const& commitHash ) {
		auto it = m_commitInfo.find( commitHash );
		if ( it != m_commitInfo.end() ) {
			return it->second;
		}

		// Try to get from Git directly
		GitWrapper git( m_upstreamPath );
		if ( !git.isValid() ) {
			return MigrationCommitInfo();
		}

		CommitInfo info = git.getCommitInfo( commitHash );
		if ( !info.hash.empty() ) {
			// Convert CommitInfo to MigrationCommitInfo
			MigrationCommitInfo migrationInfo;
			migrationInfo.hash = info.hash;
			migrationInfo.shortHash = info.shortHash;
			migrationInfo.message = info.message;
			migrationInfo.author = info.author;
			migrationInfo.fileCount = 0;  // Not available from Git
			migrationInfo.isMerge = false;  // Not available from Git
			migrationInfo.isRelevant = false;  // Not available from Git
			migrationInfo.timestamp = info.time;
			migrationInfo.files = {};  // Not available from Git
			
			m_commitInfo[commitHash] = migrationInfo;
			return migrationInfo;
		}

		return MigrationCommitInfo();
	}

		// Try to get from Git directly
		GitWrapper git( m_upstreamPath );
		if ( !git.isValid() ) {
			return MigrationCommitInfo();
		}

		CommitInfo info = git.getCommitInfo( commitHash );
		if ( !info.hash.empty() ) {
			// Convert CommitInfo to MigrationCommitInfo
			MigrationCommitInfo migrationInfo;
			migrationInfo.hash = info.hash;
			migrationInfo.shortHash = info.shortHash;
			migrationInfo.message = info.message;
			migrationInfo.author = info.author;
			migrationInfo.fileCount = 0;  // Not available from Git
			migrationInfo.isMerge = false;  // Not available from Git
			migrationInfo.isRelevant = false;  // Not available from Git
			migrationInfo.timestamp = info.time;
			migrationInfo.files = {};  // Not available from Git
			
			m_commitInfo[commitHash] = migrationInfo;
			return migrationInfo;
		}
	}

	bool CommitDiscovery::commitAffectsSources( std::string const& commitHash ) const {
		// Check if this commit touches any of our source files
		for ( auto const& file : m_sourceFiles ) {
			std::string systemdFile = file;
			systemdFile             = utils::replaceAll( systemdFile, "elogind", "systemd" );

			// This is a simplified check - in real implementation
			// we'd use Git::Wrapper to check if the commit touches the file
			if ( m_fileCommits.count( systemdFile ) && m_fileCommits.at( systemdFile ).find( commitHash ) != m_fileCommits.at( systemdFile ).end() ) {
				return true;
			}
		}

		return false;
	}

	bool CommitDiscovery::fileAffectsCommit( std::string const& commitHash, std::string const& filePath ) const {
		std::string systemdFile = filePath;
		systemdFile             = utils::replaceAll( systemdFile, "elogind", "systemd" );

		if ( m_fileCommits.count( systemdFile ) ) {
			return m_fileCommits.at( systemdFile ).find( commitHash ) != m_fileCommits.at( systemdFile ).end();
		}

		return false;
	}

} // namespace migrate
} // namespace elomig
