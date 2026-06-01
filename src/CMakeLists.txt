# =============================================================================
# This builds and installs elomig
# =============================================================================

# Source files
set( ELOMIG_SOURCES
     # Main entry point
     elomig.cpp
)

# Header files
set( ELOMIG_HEADERS
)

# Create executable
add_executable( elomig ${ELOMIG_SOURCES} ${ELOMIG_HEADERS} )

# Include directories
target_include_directories( elomig PRIVATE
                            ${CMAKE_SOURCE_DIR}/src
                            ${LIBGIT2_INCLUDE_DIRS}
)

# Link libraries
target_link_libraries( elomig PRIVATE
                       ${LIBGIT2_LIBRARIES}
                       pthread
)

# Installation
install( TARGETS elomig DESTINATION bin )
