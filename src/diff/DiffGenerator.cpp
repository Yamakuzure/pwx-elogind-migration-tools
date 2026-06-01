/**
 * @file DiffGenerator.cpp
 * @brief Implementation of diff generation
 */

#include "DiffGenerator.h"

#include "utils/FileUtil.h"
#include "utils/Logger.h"

#include <cstdio>
#include <sstream>

namespace elomig {

std::string DiffGenerator::generateUnifiedDiff( std::string const& sourcePath, std::string const& targetPath, std::string const& label ) {
	return runExternalDiff( sourcePath, targetPath );
}

std::vector< std::string > DiffGenerator::generateDiff( std::vector< std::string > const& sourceLines, std::vector< std::string > const& targetLines, int contextLines ) {
	// TODO: Implement internal diff algorithm
	// For now, use external diff
	return {};
}

std::string DiffGenerator::runExternalDiff( std::string const& source, std::string const& target ) {
	std::string cmd  = "diff -N -u " + source + " " + target + " 2>&1";

	FILE*       pipe = popen( cmd.c_str(), "r" );
	if ( !pipe ) {
		LOG_ERROR( "Failed to run diff command" );
		return "";
	}

	std::string result;
	char        buffer[4'096];

	while ( fgets( buffer, sizeof( buffer ), pipe ) != nullptr ) {
		result += buffer;
	}

	int status = pclose( pipe );

	// diff returns 0 if no differences, 1 if differences, 2 if error
	if ( WEXITSTATUS( status ) == 2 ) {
		return "";
	}

	return result;
}

} // namespace elomig
