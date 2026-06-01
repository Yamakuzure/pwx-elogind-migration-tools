/**
 * @file GitWrapper.cpp
 * @brief Implementation of Git wrapper using libgit2
 */

#include "GitWrapper.h"

#include "FileUtil.h"
#include "Logger.h"
#include "StringUtils.h"

#include <algorithm>
#include <cstring>
#include <sstream>
#include <unistd.h>

namespace elomig {

bool GitWrapper::s_initialized = false;

void GitWrapper::initializeLibGit2() {
	if ( !s_initialized ) {
		git_libgit2_init();
		s_initialized = true;
	}
}

void GitWrapper::cleanupLibGit2() {
	if ( s_initialized ) {
		git_libgit2_shutdown();
		s_initialized = false;
	}
}

GitWrapper::GitWrapper( std::string const& repoPath ) : m_repo( nullptr ), m_repoPath( repoPath ) {
	initializeLibGit2();

	int error = git_repository_open( &m_repo, repoPath.c_str() );
	if ( error != 0 ) {
		LOG_ERROR( "Failed to open repository: %s", repoPath.c_str() );
		m_repo = nullptr;
	}

	// Register cleanup on exit
	std::atexit( cleanupLibGit2 );
}

GitWrapper::~GitWrapper() {
	if ( m_repo ) {
		git_repository_free( m_repo );
		m_repo = nullptr;
	}
}

std::string GitWrapper::getHeadCommit() const {
	if ( !m_repo ) {
		return "";
	}

	git_reference* head  = nullptr;
	int            error = git_repository_head( &head, m_repo );
	if ( error != 0 ) {
		LOG_DEBUG( "No HEAD found (possibly detached)" );
		return "";
	}

	git_oid oid;
	git_oid_cpy( &oid, git_reference_target( head ) );

	char shortHash[GIT_OID_HEXSZ + 1];
	git_oid_tostr( shortHash, sizeof( shortHash ), &oid );

	git_reference_free( head );

	return std::string( shortHash );
}

std::string GitWrapper::resolveRef( std::string const& ref ) const {
	if ( !m_repo ) {
		return "";
	}

	git_object* obj   = nullptr;
	int         error = git_revparse_single( &obj, m_repo, ref.c_str() );
	if ( error != 0 ) {
		LOG_DEBUG( "Failed to resolve reference: %s", ref.c_str() );
		return "";
	}

	git_oid const* oid = git_object_id( obj );
	char           hash[GIT_OID_HEXSZ + 1];
	git_oid_tostr( hash, sizeof( hash ), oid );

	git_object_free( obj );

	return std::string( hash );
}

std::string GitWrapper::getShortHash( std::string const& ref ) const {
	std::string fullHash = resolveRef( ref );
	if ( fullHash.empty() ) {
		return "";
	}

	// Return first 10 characters as short hash
	return fullHash.substr( 0, 10 );
}

bool GitWrapper::checkout( std::string const& ref ) {
	if ( !m_repo ) {
		return false;
	}

	LOG_DEBUG( "Checking out: %s", ref.c_str() );

	// Resolve the reference
	git_object* target = nullptr;
	int         error  = git_revparse_single( &target, m_repo, ref.c_str() );
	if ( error != 0 ) {
		LOG_ERROR( "Failed to resolve reference: %s", ref.c_str() );
		return false;
	}

	// Get the commit object
	git_commit* commit = nullptr;
	error              = git_commit_lookup( &commit, m_repo, git_object_id( target ) );
	git_object_free( target );

	if ( error != 0 ) {
		LOG_ERROR( "Failed to lookup commit" );
		return false;
	}

	// Get the tree
	git_tree* tree = nullptr;
	error          = git_commit_tree( &tree, commit );
	git_commit_free( commit );

	if ( error != 0 ) {
		LOG_ERROR( "Failed to get tree from commit" );
		return false;
	}

	// Checkout the tree
	git_checkout_options checkoutOpts = GIT_CHECKOUT_OPTIONS_INIT;
	checkoutOpts.checkout_strategy    = GIT_CHECKOUT_FORCE | GIT_CHECKOUT_REMOVE_UNTRACKED;

	error                             = git_checkout_tree( m_repo, reinterpret_cast< git_object* >( tree ), &checkoutOpts );
	git_tree_free( tree );

	if ( error != 0 ) {
		LOG_ERROR( "Failed to checkout tree: %s", git_error_last()->message );
		return false;
	}

	// Set HEAD if it's a branch
	if ( utils::startsWith( ref, "refs/heads/" ) ) {
		error = git_repository_set_head( m_repo, ref.c_str() );
	} else {
		// Detached HEAD
		git_object* obj = nullptr;
		error           = git_revparse_single( &obj, m_repo, ref.c_str() );
		if ( error == 0 ) {
			error = git_repository_set_head_detached( m_repo, git_object_id( obj ) );
			git_object_free( obj );
		}
	}

	if ( error != 0 ) {
		LOG_WARNING( "Failed to set HEAD: %s", git_error_last()->message );
		// Not fatal, tree is still checked out
	}

	LOG_DEBUG( "Checkout successful" );
	return true;
}

std::vector< std::string > GitWrapper::revList( std::string const& from, std::string const& to, std::string const& path, bool noMerges, bool reverse ) const {
	std::vector< std::string > result;

	if ( !m_repo ) {
		return result;
	}

	// Build revwalk
	git_revwalk* walker = nullptr;
	int          error  = git_revwalk_new( &walker, m_repo );
	if ( error != 0 ) {
		LOG_ERROR( "Failed to create revwalk" );
		return result;
	}

	// Sort options
	if ( reverse ) {
		git_revwalk_sorting( walker, GIT_SORT_TIME );
	} else {
		git_revwalk_sorting( walker, GIT_SORT_TIME | GIT_SORT_REVERSE );
	}

	// Push the "to" reference
	// git_oid toOid; // Unused
	error = git_revparse_single( nullptr, m_repo, to.c_str() );
	if ( error == 0 ) {
		git_object* toObj = nullptr;
		git_revparse_single( &toObj, m_repo, to.c_str() );
		git_revwalk_push( walker, git_object_id( toObj ) );
		git_object_free( toObj );
	} else {
		LOG_DEBUG( "Failed to resolve 'to' reference: %s", to.c_str() );
		git_revwalk_free( walker );
		return result;
	}

	// Hide the "from" reference
	if ( !from.empty() ) {
		git_object* fromObj = nullptr;
		error               = git_revparse_single( &fromObj, m_repo, from.c_str() );
		if ( error == 0 ) {
			git_revwalk_hide( walker, git_object_id( fromObj ) );
			git_object_free( fromObj );
		}
	}

	// Walk the commits
	git_oid oid;
	while ( ( error = git_revwalk_next( &oid, walker ) ) == 0 ) {
		// Skip merges if requested
		if ( noMerges ) {
			git_commit* commit = nullptr;
			if ( git_commit_lookup( &commit, m_repo, &oid ) == 0 ) {
				size_t parentCount = git_commit_parentcount( commit );
				git_commit_free( commit );

				if ( parentCount > 1 ) {
					continue; // Skip merge commit
				}
			}
		}

		// Check path if specified
		if ( !path.empty() ) {
			// For simplicity, we include all commits here
			// A full implementation would check tree diffs
			// This is a known limitation
		}

		char hash[GIT_OID_HEXSZ + 1];
		git_oid_tostr( hash, sizeof( hash ), &oid );
		result.push_back( hash );
	}

	git_revwalk_free( walker );

	return result;
}

std::vector< std::string > GitWrapper::getFileCommits( std::string const& from, std::string const& to, std::string const& filePath ) const {
	// For now, use the general revList and filter later
	// A more efficient implementation would use libgit2's diff API
	return revList( from, to, filePath, true, false );
}

CommitInfo GitWrapper::getCommitInfo( std::string const& hash ) const {
	CommitInfo info;

	if ( !m_repo ) {
		return info;
	}

	git_commit* commit = nullptr;
	git_oid     oid;

	int         error = git_oid_fromstr( &oid, hash.c_str() );
	if ( error != 0 ) {
		return info;
	}

	error = git_commit_lookup( &commit, m_repo, &oid );
	if ( error != 0 ) {
		return info;
	}

	// Get basic info
	info.hash           = hash;
	info.shortHash      = hash.substr( 0, 10 );

	char const* message = git_commit_message( commit );
	if ( message ) {
		// Get first line
		char const* newline = strchr( message, '\n' );
		if ( newline ) {
			info.message = std::string( message, newline - message );
		} else {
			info.message = message;
		}
	}

	git_signature const* author = git_commit_author( commit );
	if ( author ) {
		info.author   = author->name ? author->name : "";
		info.email    = author->email ? author->email : "";
		info.time     = author->when.time;
		info.timezone = author->when.offset;
	}

	git_commit_free( commit );

	return info;
}

std::string GitWrapper::getCommitMessage( std::string const& hash ) const {
	CommitInfo info = getCommitInfo( hash );
	return info.message;
}

bool GitWrapper::refExists( std::string const& ref ) const {
	if ( !m_repo ) {
		return false;
	}

	git_reference* gitRef = nullptr;
	int            error  = git_reference_lookup( &gitRef, m_repo, ref.c_str() );

	if ( error == 0 ) {
		git_reference_free( gitRef );
		return true;
	}

	// Try as shorthand
	return !resolveRef( ref ).empty();
}

std::string GitWrapper::getCurrentBranch() const {
	if ( !m_repo ) {
		return "";
	}

	git_reference* head  = nullptr;
	int            error = git_repository_head( &head, m_repo );
	if ( error != 0 ) {
		return ""; // Detached HEAD
	}

	std::string name = git_reference_name( head );
	git_reference_free( head );

	// Remove "refs/heads/" prefix
	std::string const prefix = "refs/heads/";
	if ( utils::startsWith( name, prefix ) ) {
		return name.substr( prefix.length() );
	}

	return name;
}

bool GitWrapper::isClean() const {
	if ( !m_repo ) {
		return false;
	}

	git_status_options opts   = GIT_STATUS_OPTIONS_INIT;
	git_status_list*   status = nullptr;

	int                error  = git_status_list_new( &status, m_repo, &opts );
	if ( error != 0 ) {
		return false;
	}

	size_t count = git_status_list_entrycount( status );
	git_status_list_free( status );

	return count == 0;
}

// Free functions

std::vector< std::string > generateFormatPatch( std::string const& repoPath, std::string const& commitHash, std::string const& outputDir, int startNumber ) {
	std::vector< std::string > result;

	// Use git command directly for format-patch
	// libgit2 doesn't provide this functionality

	std::string cmd = utils::format(
		"cd %s && git format-patch --find-copies --find-copies-harder --numbered "
		"--output-directory %s --start-number %d -1 %s 2>&1",
		repoPath.c_str(),
		outputDir.c_str(),
		startNumber,
		commitHash.c_str()
	);

	FILE* pipe = popen( cmd.c_str(), "r" );
	if ( !pipe ) {
		LOG_ERROR( "Failed to run git format-patch" );
		return result;
	}

	char buffer[256];
	while ( fgets( buffer, sizeof( buffer ), pipe ) != nullptr ) {
		std::string line = utils::trim( buffer );
		if ( !line.empty() && utils::endsWith( line, ".patch" ) ) {
			result.push_back( utils::getBaseName( line ) );
		}
	}

	pclose( pipe );

	return result;
}

bool applyPatch( std::string const& repoPath, std::string const& patchContent, bool threeWay ) {
	// Write patch to temp file
	std::string tempPatch = "/tmp/elomig_patch_" + std::to_string( getpid() ) + ".patch";
	if ( !utils::writeFile( tempPatch, patchContent ) ) {
		LOG_ERROR( "Failed to write temporary patch file" );
		return false;
	}

	// Use git am command
	std::string cmd = utils::format( "cd %s && git am %s %s < %s 2>&1", repoPath.c_str(), threeWay ? "--3way" : "", "--continue", tempPatch.c_str() );

	int         ret = system( cmd.c_str() );
	utils::deleteFile( tempPatch );

	return ( ret == 0 );
}

bool gitAdd( std::string const& repoPath, std::vector< std::string > const& files ) {
	if ( files.empty() ) {
		return true;
	}

	std::string cmd = "cd " + repoPath + " && git add";
	for ( auto const& file : files ) {
		cmd += " \"" + file + "\"";
	}

	int ret = system( cmd.c_str() );
	return ( ret == 0 );
}

} // namespace elomig
