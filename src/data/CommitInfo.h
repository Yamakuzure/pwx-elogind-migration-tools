/**
 * @file CommitInfo.h
 * @brief Extended commit information structure
 *
 * Additional commit metadata used during migration.
 */

#ifndef ELOMIG_COMMIT_INFO_EXTENDED_H
#define ELOMIG_COMMIT_INFO_EXTENDED_H

#include <cstdint>
#include <string>
#include <vector>

namespace elomig {

/**
 * @brief Extended commit information for migration tracking
 */
struct MigrationCommitInfo {
	std::string                hash;       ///< Full commit hash
	std::string                shortHash;  ///< Short hash
	std::string                message;    ///< Commit message
	std::string                author;     ///< Author
	int                        fileCount;  ///< Number of files touched
	bool                       isMerge;    ///< True if merge commit
	bool                       isRelevant; ///< True if touches relevant files
	int64_t                    timestamp;  ///< Commit timestamp
	std::vector< std::string > files;      ///< Files modified

	MigrationCommitInfo() : fileCount( 0 ), isMerge( false ), isRelevant( false ), timestamp( 0 ) {}
};

/**
 * @brief Mutual commit tracking for CSV file
 */
struct MutualCommitEntry {
	std::string upstreamPath; ///< Upstream repository path
	std::string refId;        ///< Reference ID (branch/tag)
	std::string mutual;       ///< Last mutual commit
	std::string src;          ///< Last upstream commit
	std::string tgt;          ///< Last local commit

	MutualCommitEntry() = default;

	MutualCommitEntry( std::string const& path, std::string const& ref ) : upstreamPath( path ), refId( ref ) {}
};

} // namespace elomig

#endif // ELOMIG_COMMIT_INFO_EXTENDED_H
