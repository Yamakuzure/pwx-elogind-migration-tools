/**
 * @file FileUtil.cpp
 * @brief Implementation of file utility functions
 */

#include "FileUtil.h"

#include "StringUtils.h"

#include <algorithm>
#include <fstream>
#include <glob.h>
#include <sstream>

namespace elomig {
namespace utils {

	bool fileExists( std::string const& path ) {
		return fs::exists( path ) && fs::is_regular_file( path );
	}

	bool isDirectory( std::string const& path ) {
		return fs::exists( path ) && fs::is_directory( path );
	}

	bool createDirectory( std::string const& path ) {
		try {
			return fs::create_directories( path );
		} catch ( fs::filesystem_error const& e ) {
			return false;
		}
	}

	bool readFile( std::string const& path, std::vector< std::string >& lines ) {
		std::ifstream file( path );
		if ( !file.is_open() ) {
			return false;
		}

		std::string line;
		while ( std::getline( file, line ) ) {
			// Remove trailing CR if present (Windows line endings)
			if ( !line.empty() && line.back() == '\r' ) {
				line.pop_back();
			}
			lines.push_back( line );
		}

		return true;
	}

	std::string readFileAsString( std::string const& path ) {
		std::ifstream file( path );
		if ( !file.is_open() ) {
			return "";
		}

		std::ostringstream buffer;
		buffer << file.rdbuf();
		return buffer.str();
	}

	bool writeFile( std::string const& path, std::vector< std::string > const& lines ) {
		std::ofstream file( path );
		if ( !file.is_open() ) {
			return false;
		}

		for ( auto const& line : lines ) {
			file << line << "\n";
		}

		return true;
	}

	bool writeFile( std::string const& path, std::string const& content ) {
		std::ofstream file( path );
		if ( !file.is_open() ) {
			return false;
		}

		file << content;
		return true;
	}

	std::string getAbsolutePath( std::string const& path ) {
		try {
			return fs::absolute( path ).string();
		} catch ( fs::filesystem_error const& e ) {
			return path;
		}
	}

	std::string getDirectoryName( std::string const& path ) {
		try {
			return fs::path( path ).parent_path().string();
		} catch ( fs::filesystem_error const& e ) {
			return "";
		}
	}

	std::string getBaseName( std::string const& path ) {
		try {
			return fs::path( path ).filename().string();
		} catch ( fs::filesystem_error const& e ) {
			return "";
		}
	}

	std::string getExtension( std::string const& path ) {
		try {
			return fs::path( path ).extension().string();
		} catch ( fs::filesystem_error const& e ) {
			return "";
		}
	}

	std::string getCurrentWorkingDirectory() {
		try {
			return fs::current_path().string();
		} catch ( fs::filesystem_error const& e ) {
			return ".";
		}
	}

	std::vector< std::string > findFiles( std::string const& rootDir, std::vector< std::string > const& patterns, std::set< std::string > const& excludeDirs ) {
		std::vector< std::string > result;

		if ( !isDirectory( rootDir ) ) {
			return result;
		}

		try {
			for ( auto const& entry : fs::recursive_directory_iterator( rootDir ) ) {
				if ( !entry.is_regular_file() ) {
					continue;
				}

				// Check if in excluded directory
				std::string path     = entry.path().string();
				bool        excluded = false;

				for ( auto const& excl : excludeDirs ) {
					if ( path.find( "/" + excl + "/" ) != std::string::npos || path.find( "/" + excl ) != std::string::npos ) {
						excluded = true;
						break;
					}
				}

				if ( excluded ) {
					continue;
				}

				// Check if matches any pattern
				std::string filename = entry.path().filename().string();
				for ( auto const& pattern : patterns ) {
					// Simple glob-style matching
					bool matches = false;

					if ( pattern[0] == '*' ) {
						// Extension pattern like *.c
						std::string ext = pattern.substr( 1 );
						if ( utils::endsWith( filename, ext ) ) {
							matches = true;
						}
					} else if ( pattern.find( '*' ) != std::string::npos ) {
						// Complex pattern - use regex or simple matching
						// For now, simple implementation
						matches = ( filename.find( pattern ) != std::string::npos );
					} else {
						// Exact match
						matches = ( filename == pattern );
					}

					if ( matches ) {
						result.push_back( path );
						break;
					}
				}
			}
		} catch ( fs::filesystem_error const& e ) {
			// Ignore errors during directory traversal
		}

		// Sort results for consistent ordering
		std::sort( result.begin(), result.end() );

		return result;
	}

	bool copyFile( std::string const& source, std::string const& dest ) {
		try {
			fs::copy_file( source, dest, fs::copy_options::overwrite_existing );
			return true;
		} catch ( fs::filesystem_error const& e ) {
			return false;
		}
	}

	bool deleteFile( std::string const& path ) {
		try {
			if ( fs::exists( path ) ) {
				return fs::remove( path );
			}
			return true;
		} catch ( fs::filesystem_error const& e ) {
			return false;
		}
	}

	ssize_t getFileSize( std::string const& path ) {
		try {
			return static_cast< ssize_t >( fs::file_size( path ) );
		} catch ( fs::filesystem_error const& e ) {
			return -1;
		}
	}

	bool hasExtension( std::string const& path, std::vector< std::string > const& extensions ) {
		std::string ext = getExtension( path );

		for ( auto const& checkExt : extensions ) {
			if ( ext == checkExt ) {
				return true;
			}
		}

		return false;
	}

	std::string normalizePath( std::string const& path ) {
		try {
			return fs::weakly_canonical( path ).string();
		} catch ( fs::filesystem_error const& e ) {
			return path;
		}
	}

	std::string getRelativePath( std::string const& path, std::string const& base ) {
		try {
			fs::path p( path );
			fs::path b( base );
			return fs::relative( p, b ).string();
		} catch ( fs::filesystem_error const& e ) {
			return path;
		}
	}

	void cleanupTempFiles( std::string const& directory, std::vector< std::string > const& patterns ) {
		if ( !isDirectory( directory ) ) {
			return;
		}

		try {
			for ( auto const& entry : fs::directory_iterator( directory ) ) {
				if ( !entry.is_regular_file() ) {
					continue;
				}

				std::string filename = entry.path().filename().string();

				for ( auto const& pattern : patterns ) {
					bool matches = false;

					if ( pattern[0] == '*' ) {
						std::string ext = pattern.substr( 1 );
						if ( utils::endsWith( filename, ext ) ) {
							matches = true;
						}
					} else {
						matches = ( filename == pattern );
					}

					if ( matches ) {
						fs::remove( entry.path() );
						break;
					}
				}
			}
		} catch ( fs::filesystem_error const& e ) {
			// Ignore errors during cleanup
		}
	}

} // namespace utils
} // namespace elomig
