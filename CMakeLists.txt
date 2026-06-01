# =============================================================================
# CMakeLists.txt for elomig - elogind Migration Tool
# =============================================================================
# This file defines the main build configuration for elomig, a unified tool for
# migrating systemd commits to elogind.
# =============================================================================

cmake_minimum_required( VERSION 3.20 )
project( elomig VERSION 1.0.0 LANGUAGES CXX )

# C++17 standard required
set( CMAKE_CXX_STANDARD 17 )
set( CMAKE_CXX_STANDARD_REQUIRED ON )
set( CMAKE_CXX_EXTENSIONS OFF )

# Compiler flags
set( CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wpedantic -Werror" )
set( CMAKE_CXX_FLAGS_DEBUG "-ggdb -Og -DDEBUG" )
set( CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG" )

# Find libgit2
find_package( libgit2 REQUIRED )
if ( NOT LIBGIT2_FOUND )
	find_package( PkgConfig QUIET )
	if ( PkgConfig_FOUND )
		pkg_check_modules( LIBGIT2 libgit2 )
	endif ()
endif ()


# Sources are in ./src
add_subdirectory( src )


# Print configuration summary
message( STATUS "" )
message( STATUS "elomig Configuration Summary:" )
message( STATUS "  Version:        ${PROJECT_VERSION}" )
message( STATUS "  Build Type:     ${CMAKE_BUILD_TYPE}" )
message( STATUS "  C++ Compiler:   ${CMAKE_CXX_COMPILER}" )
message( STATUS "  C++ Flags:      ${CMAKE_CXX_FLAGS}" )
message( STATUS "  libgit2:        ${LIBGIT2_LIBRARIES}" )
message( STATUS "" )