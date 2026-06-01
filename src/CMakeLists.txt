# =============================================================================
# CMakeLists.txt for elomig - elogind Migration Tool
# =============================================================================
# This file defines the build configuration for elomig, a unified tool for
# migrating systemd commits to elogind.
# =============================================================================

cmake_minimum_required(VERSION 3.20)
project(elomig VERSION 1.0.0 LANGUAGES CXX)

# C++17 standard required
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Compiler flags
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wpedantic")
set(CMAKE_CXX_FLAGS_DEBUG "-g -O0 -DDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG")

# Find libgit2 - prefer system version over bundled
find_package(PkgConfig QUIET)
if(PkgConfig_FOUND)
    pkg_check_modules(LIBGIT2 libgit2)
endif()

if(NOT LIBGIT2_FOUND)
    # Try to find bundled libgit2
    if(EXISTS "${CMAKE_SOURCE_DIR}/../libgit2-1.9.4")
        message(STATUS "Using bundled libgit2")
        set(LIBGIT2_INCLUDE_DIRS "${CMAKE_SOURCE_DIR}/../libgit2-1.9.4/include")
        set(LIBGIT2_LIBRARIES "git2")
    else()
        find_package(libgit2 REQUIRED)
    endif()
endif()

# Source files
set(ELOMIG_SOURCES
    # Main entry point
    elomig.cpp
    
    # Core utilities
    utils/Logger.cpp
    utils/StringUtils.cpp
    utils/FileUtil.cpp
    utils/GitWrapper.cpp
    utils/ThreadPool.cpp
    
    # Data structures
    data/Hunk.cpp
    data/FileDiff.cpp
    data/Patch.cpp
    data/CommitInfo.cpp
    
    # Diff processing
    diff/DiffGenerator.cpp
    diff/DiffParser.cpp
    
    # Mask block handling
    mask/MaskDetector.cpp
    mask/MaskHandler.cpp
    mask/ShellProcessor.cpp
    mask/XMLProcessor.cpp
    
    # Name reversion
    reversion/KindDetector.cpp
    reversion/NameReverter.cpp
    
    # Include analysis
    include/IncludeAnalyzer.cpp
    include/IncludeReconciler.cpp
    
    # Hunk refactoring pipeline
    refactor/HunkRefactorer.cpp
    refactor/MaskChecker.cpp
    refactor/MuslChecker.cpp
    refactor/DebugChecker.cpp
    refactor/CommentChecker.cpp
    refactor/UselessChecker.cpp
    refactor/EmptyMaskChecker.cpp
    refactor/FunctionProtector.cpp
    refactor/IncludeHandler.cpp
    
    # Check tree mode
    checktree/CheckTree.cpp
    checktree/FileProcessor.cpp
    checktree/PatchBuilder.cpp
    
    # Migrate tree mode
    migrate/MigrateTree.cpp
    migrate/CommitDiscovery.cpp
    migrate/PatchGenerator.cpp
    migrate/PatchApplier.cpp
    migrate/CommitFile.cpp
)

# Header files
set(ELOMIG_HEADERS
    # Core utilities
    utils/Logger.h
    utils/StringUtils.h
    utils/FileUtil.h
    utils/GitWrapper.h
    
    # Data structures
    data/Hunk.h
    data/FileDiff.h
    data/Patch.h
    data/CommitInfo.h
    
    # Diff processing
    diff/DiffGenerator.h
    diff/DiffParser.h
    
    # Mask block handling
    mask/MaskDetector.h
    mask/MaskHandler.h
    mask/ShellProcessor.h
    mask/XMLProcessor.h
    
    # Name reversion
    reversion/NameReverter.h
    reversion/KindDetector.h
    
    # Include analysis
    include/IncludeAnalyzer.h
    include/IncludeReconciler.h
    
    # Hunk refactoring pipeline
    refactor/HunkRefactorer.h
    refactor/MaskChecker.h
    refactor/MuslChecker.h
    refactor/DebugChecker.h
    refactor/CommentChecker.h
    refactor/UselessChecker.h
    refactor/EmptyMaskChecker.h
    refactor/FunctionProtector.h
    refactor/IncludeHandler.h
    
    # Check tree mode
    checktree/CheckTree.h
    checktree/FileProcessor.h
    checktree/PatchBuilder.h
    
    # Migrate tree mode
    migrate/MigrateTree.h
    migrate/CommitDiscovery.h
    migrate/PatchGenerator.h
    migrate/PatchApplier.h
    migrate/CommitFile.h
)

# Create executable
add_executable(elomig ${ELOMIG_SOURCES} ${ELOMIG_HEADERS})

# Include directories
target_include_directories(elomig PRIVATE
    ${CMAKE_SOURCE_DIR}
    ${LIBGIT2_INCLUDE_DIRS}
)

# Link libraries
target_link_libraries(elomig PRIVATE
    ${LIBGIT2_LIBRARIES}
    pthread
)

# Installation
install(TARGETS elomig DESTINATION bin)

# Print configuration summary
message(STATUS "")
message(STATUS "elomig Configuration Summary:")
message(STATUS "  Version:        ${PROJECT_VERSION}")
message(STATUS "  Build Type:     ${CMAKE_BUILD_TYPE}")
message(STATUS "  C++ Compiler:   ${CMAKE_CXX_COMPILER}")
message(STATUS "  C++ Flags:      ${CMAKE_CXX_FLAGS}")
message(STATUS "  libgit2:        ${LIBGIT2_LIBRARIES}")
message(STATUS "")
