# =============================================================================
# Convenience Makefile for elomig
# =============================================================================
# This Makefile provides easy access to common build configurations.
# Usage:
#   make              - Build release version
#   make DEBUG=YES    - Build debug version
#   make clean        - Clean all build artifacts
#   make help         - Show this help
# =============================================================================

.PHONY: all release debug clean help test

# Default target
all: release

# Configuration
BUILD_DIR_RELEASE = cmake-build
BUILD_DIR_DEBUG = cmake-build_d
CMAKE = cmake
NINJA = ninja

# Check if DEBUG is set
ifdef DEBUG
    ifeq ($(DEBUG),YES)
        BUILD_DIR = $(BUILD_DIR_DEBUG)
        BUILD_TYPE = Debug
    else
        BUILD_DIR = $(BUILD_DIR_RELEASE)
        BUILD_TYPE = Release
    endif
else
    BUILD_DIR = $(BUILD_DIR_RELEASE)
    BUILD_TYPE = Release
endif

# Compiler settings
CXX = g++-16
CXXFLAGS = -std=c++17 -Wall -Wextra -Wpedantic

# Main targets
release:
	@echo "Building elomig (Release)..."
	@mkdir -p $(BUILD_DIR_RELEASE)
	@cd $(BUILD_DIR_RELEASE) && $(CMAKE) -G Ninja -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_COMPILER=$(CXX) ../src
	@cd $(BUILD_DIR_RELEASE) && $(NINJA)
	@echo "Build complete: $(BUILD_DIR_RELEASE)/elomig"

debug:
	@echo "Building elomig (Debug)..."
	@mkdir -p $(BUILD_DIR_DEBUG)
	@cd $(BUILD_DIR_DEBUG) && $(CMAKE) -G Ninja -DCMAKE_BUILD_TYPE=Debug -DCMAKE_CXX_COMPILER=$(CXX) ../src
	@cd $(BUILD_DIR_DEBUG) && $(NINJA)
	@echo "Build complete: $(BUILD_DIR_DEBUG)/elomig"

# Clean build artifacts
clean:
	@echo "Cleaning build directories..."
	@rm -rf $(BUILD_DIR_RELEASE)
	@rm -rf $(BUILD_DIR_DEBUG)
	@echo "Clean complete."

# Run basic tests
test: release
	@echo "Running basic tests..."
	@./$(BUILD_DIR_RELEASE)/elomig --help
	@echo "Tests complete."

# Help target
help:
	@echo "elomig Build System"
	@echo "==================="
	@echo ""
	@echo "Targets:"
	@echo "  all (default)     - Build release version"
	@echo "  release           - Build release version (optimized)"
	@echo "  debug             - Build debug version (with symbols)"
	@echo "  clean             - Remove all build artifacts"
	@echo "  test              - Build and run basic tests"
	@echo "  help              - Show this help message"
	@echo ""
	@echo "Options:"
	@echo "  DEBUG=YES         - Build with debug symbols"
	@echo ""
	@echo "Examples:"
	@echo "  make              - Build release version"
	@echo "  make DEBUG=YES    - Build debug version"
	@echo "  make clean        - Clean everything"
	@echo "  make test         - Build and test"
	@echo ""
	@echo "Build Directories:"
	@echo "  Release: $(BUILD_DIR_RELEASE)"
	@echo "  Debug:   $(BUILD_DIR_DEBUG)"
