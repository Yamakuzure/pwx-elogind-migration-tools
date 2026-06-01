/**
 * @file elomig.cpp
 * @brief Main entry point for elomig - elogind Migration Tool
 *
 * Unified tool for migrating systemd commits to elogind.
 * Combines functionality from check_tree.pl and migrate_tree.pl.
 */

#include "checktree/CheckTree.h"
#include "migrate/MigrateTree.h"
#include "utils/FileUtil.h"
#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <cstdlib>
#include <cstring>
#include <getopt.h>
#include <iostream>
#include <string>
#include <vector>

using namespace elomig;

/**
 * @brief Program version
 */
static char const* VERSION = "1.0.0";

/**
 * @brief Program name
 */
static char const* PROGNAME = "elomig";

/**
 * @brief Short usage message
 */
static char const* USAGE_SHORT = R"(
Usage: elomig [OPTIONS] --upstream <path>
       elomig migrate [OPTIONS] --upstream <path> --refid <ref>

Unified elogind migration tool.

Modes:
  (default)         Check tree mode (like check_tree.pl)
  migrate           Migration mode (like migrate_tree.pl)

Mandatory options:
  -u, --upstream <path>   Path to upstream systemd tree

Check tree options:
  -c, --commit <ref>      Checkout specific commit in upstream
  --stay                  Don't restore upstream HEAD after --commit
  -f, --file <path>       Process only specified file(s)
  --create                Allow creation of non-existent files
  -s, --source <path>     Use different source directory
  -D, --debug             Enable debug output
  -j, --threads <num>     Number of threads for parallel processing

Migration options:
  -r, --refid <ref>       Reference to migrate (branch, tag, commit)
  --advance               Use last src commit as new mutual commit
  -o, --output <dir>      Output directory for patches

General options:
  -h, --help              Show help message
  -v, --version           Show version
)";

/**
 * @brief Show version information
 */
void showVersion() {
	std::cout << PROGNAME << " version " << VERSION << std::endl;
	std::cout << "elogind migration tool" << std::endl;
}

/**
 * @brief Show help message
 * @param detailed If true, show detailed help
 */
void showHelp( bool detailed = false ) {
	if ( detailed ) {
		// TODO: Add detailed help from POD-style documentation
		std::cout << USAGE_SHORT << std::endl;
	} else {
		std::cout << USAGE_SHORT << std::endl;
	}
}

/**
 * @brief Parse command line arguments
 * @param argc Argument count
 * @param argv Argument vector
 * @param mode Output: operation mode ("check" or "migrate")
 * @param options Output: parsed options map
 * @return True if parsing succeeded
 */
bool parseArguments( int argc, char* argv[], std::string& mode, std::vector< std::pair< std::string, std::string > >& options ) {
	// Check for mode selector (first non-option argument)
	int argIndex = 1;
	while ( argIndex < argc && argv[argIndex][0] == '-' ) {
		argIndex++;
	}

	if ( argIndex < argc ) {
		std::string firstArg = argv[argIndex];
		if ( firstArg == "migrate" ) {
			mode = "migrate";
			// Remove migrate from argv by shifting
			for ( int i = argIndex; i < argc - 1; i++ ) {
				argv[i] = argv[i + 1];
			}
			argc--;
		} else if ( firstArg == "check" || firstArg == "check-tree" ) {
			mode = "check";
			for ( int i = argIndex; i < argc - 1; i++ ) {
				argv[i] = argv[i + 1];
			}
			argc--;
		}
	}

	// Default mode
	if ( mode.empty() ) {
		mode = "check";
	}

	// Parse options
	static struct option longOptions[] = {
		{ "help",     no_argument,       nullptr, 'h' },
                { "version",  no_argument,       nullptr, 'v' },
		{ "debug",    no_argument,       nullptr, 'D' },
                { "upstream", required_argument, nullptr, 'u' },
		{ "commit",   required_argument, nullptr, 'c' },
                { "stay",     no_argument,       nullptr, 'S' },
		{ "file",     required_argument, nullptr, 'f' },
                { "create",   no_argument,       nullptr, 'C' },
		{ "source",   required_argument, nullptr, 's' },
                { "threads",  required_argument, nullptr, 'j' },
		{ "refid",    required_argument, nullptr, 'r' },
                { "advance",  no_argument,       nullptr, 'A' },
		{ "output",   required_argument, nullptr, 'o' },
                { nullptr,    0,                 nullptr, 0   }
	};

	int opt;
	while ( ( opt = getopt_long( argc, argv, "hvDu:c:Sf:Cs:j:r:Ao:", longOptions, nullptr ) ) != -1 ) {
		switch ( opt ) {
			case 'h':
				showHelp( true );
				exit( 0 );

			case 'v':
				showVersion();
				exit( 0 );

			case 'D':
				options.push_back( { "debug", "true" } );
				break;

			case 'u':
				options.push_back( { "upstream", optarg } );
				break;

			case 'c':
				options.push_back( { "commit", optarg } );
				break;

			case 'S':
				options.push_back( { "stay", "true" } );
				break;

			case 'f':
				options.push_back( { "file", optarg } );
				break;

			case 'C':
				options.push_back( { "create", "true" } );
				break;

			case 's':
				options.push_back( { "source", optarg } );
				break;

			case 'j':
				options.push_back( { "threads", optarg } );
				break;

			case 'r':
				options.push_back( { "refid", optarg } );
				break;

			case 'A':
				options.push_back( { "advance", "true" } );
				break;

			case 'o':
				options.push_back( { "output", optarg } );
				break;

			default:
				std::cerr << "Unknown option or missing argument" << std::endl;
				return false;
		}
	}

	return true;
}

/**
 * @brief Get option value from parsed options
 * @param options Options vector
 * @param key Option key
 * @param defaultValue Default value if not found
 * @return Option value or default
 */
std::string getOption( std::vector< std::pair< std::string, std::string > > const& options, std::string const& key, std::string const& defaultValue = "" ) {
	for ( auto const& opt : options ) {
		if ( opt.first == key ) {
			return opt.second;
		}
	}
	return defaultValue;
}

/**
 * @brief Check if option is set
 * @param options Options vector
 * @param key Option key
 * @return True if option is set
 */
bool hasOption( std::vector< std::pair< std::string, std::string > > const& options, std::string const& key ) {
	for ( auto const& opt : options ) {
		if ( opt.first == key ) {
			return true;
		}
	}
	return false;
}

/**
 * @brief Get all values for a multi-value option
 * @param options Options vector
 * @param key Option key
 * @return Vector of values
 */
std::vector< std::string > getOptionValues( std::vector< std::pair< std::string, std::string > > const& options, std::string const& key ) {
	std::vector< std::string > values;
	for ( auto const& opt : options ) {
		if ( opt.first == key ) {
			values.push_back( opt.second );
		}
	}
	return values;
}

/**
 * @brief Validate options for check mode
 * @param options Parsed options
 * @return True if valid
 */
bool validateCheckOptions( std::vector< std::pair< std::string, std::string > > const& options ) {
	if ( !hasOption( options, "upstream" ) ) {
		std::cerr << "Error: --upstream is required" << std::endl;
		return false;
	}

	// --create requires --file
	if ( hasOption( options, "create" ) && !hasOption( options, "file" ) ) {
		std::cerr << "Error: --create requires --file" << std::endl;
		return false;
	}

	// --stay requires --commit
	if ( hasOption( options, "stay" ) && !hasOption( options, "commit" ) ) {
		std::cerr << "Error: --stay requires --commit" << std::endl;
		return false;
	}

	return true;
}

/**
 * @brief Validate options for migrate mode
 * @param options Parsed options
 * @return True if valid
 */
bool validateMigrateOptions( std::vector< std::pair< std::string, std::string > > const& options ) {
	if ( !hasOption( options, "upstream" ) ) {
		std::cerr << "Error: --upstream is required" << std::endl;
		return false;
	}

	if ( !hasOption( options, "refid" ) ) {
		std::cerr << "Error: --refid is required for migrate mode" << std::endl;
		return false;
	}

	// --advance and --commit are mutually exclusive
	if ( hasOption( options, "advance" ) && hasOption( options, "commit" ) ) {
		std::cerr << "Error: --advance and --commit are mutually exclusive" << std::endl;
		return false;
	}

	return true;
}

/**
 * @brief Main entry point
 * @param argc Argument count
 * @param argv Argument vector
 * @return Exit code (0=success, 1=error, 42=signal)
 */
int main( int argc, char* argv[] ) {
	std::string                                          mode = "check";
	std::vector< std::pair< std::string, std::string > > options;

	// Parse command line
	if ( !parseArguments( argc, argv, mode, options ) ) {
		std::cerr << USAGE_SHORT << std::endl;
		return 1;
	}

	// Validate options based on mode
	bool valid = false;
	if ( mode == "check" ) {
		valid = validateCheckOptions( options );
	} else if ( mode == "migrate" ) {
		valid = validateMigrateOptions( options );
	}

	if ( !valid ) {
		std::cerr << USAGE_SHORT << std::endl;
		return 1;
	}

	// Initialize logger
	bool        debugMode    = hasOption( options, "debug" );
	std::string upstreamPath = getOption( options, "upstream" );

	// Build log file name from upstream basename
	std::string upstreamBase = utils::getBaseName( upstreamPath );
	std::string logFile      = upstreamBase + "-" + Logger::getInstance().getTimestamp().substr( 0, 10 ) + ".log";
	logFile                  = utils::replaceAll( logFile, ":", "-" ); // Remove colons for filesystem compatibility

	auto& logger             = Logger::getInstance();
	logger.initialize( logFile, LogLevel::STATUS, debugMode );

	LOG_STATUS( "Program Start" );
	LOG_DEBUG( "Mode: %s", mode.c_str() );
	LOG_DEBUG( "Upstream: %s", upstreamPath.c_str() );

	int result = 0;

	try {
		// Execute appropriate mode
		if ( mode == "check" ) {
			// Check tree mode
			checktree::CheckTree checkTree;

			checkTree.setUpstreamPath( upstreamPath );
			checkTree.setCommit( getOption( options, "commit" ) );
			checkTree.setStay( hasOption( options, "stay" ) );
			checkTree.setDebugMode( debugMode );
			checkTree.setCreateMode( hasOption( options, "create" ) );
			checkTree.setSourcePath( getOption( options, "source" ) );

			// Set thread count
			std::string threadStr = getOption( options, "threads" );
			if ( !threadStr.empty() ) {
				try {
					size_t threads = std::stoul( threadStr );
					if ( threads > 0 ) {
						checkTree.setThreadCount( threads );
					}
				} catch ( ... ) {
					// Ignore invalid thread count
				}
			}

			auto files = getOptionValues( options, "file" );
			for ( auto const& file : files ) {
				checkTree.addFile( file );
			}

			result = checkTree.run() ? 0 : 1;

		} else if ( mode == "migrate" ) {
			// Migration mode
			migrate::MigrateTree migrator;

			migrator.setUpstreamPath( upstreamPath );
			migrator.setRefId( getOption( options, "refid" ) );
			migrator.setAdvance( hasOption( options, "advance" ) );
			migrator.setMutualCommit( getOption( options, "commit" ) );
			migrator.setOutputPath( getOption( options, "output" ) );
			migrator.setDebugMode( debugMode );

			result = migrator.run() ? 0 : 1;
		}

	} catch ( std::exception const& e ) {
		LOG_ERROR( "Unhandled exception: %s", e.what() );
		result = 1;
	} catch ( ... ) {
		LOG_ERROR( "Unknown error occurred" );
		result = 1;
	}

	LOG_STATUS( "Program End" );

	return logger.getGlobalError() != 0 ? logger.getGlobalError() : result;
}
