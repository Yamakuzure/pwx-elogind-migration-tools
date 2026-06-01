# -----------------------------------------------------------------------------
# --- ======= Wrapping Makefile for the EWX elogind Migration Tool ======== ---
# ---    Without a target, the elomig tool is built and 'installed' here.   ---
# -----------------------------------------------------------------------------
#
export
LC_ALL=C
#
#
# -------------------------------------------------------------------------------------------------
# Chose the configuration to use:
# DEBUG     : YES or NO
# DEBUG_LOCK: If YES, certain lock/unlock macros print extra messages (noisy!)
# JUST_PRINT: Set this to YES to have make/ninja show all build commands
#             Defaults to YES if make is called with --just-print/-n option, and to NO otherwise.
# SANITIZE_ADDRESS: Set to YES to build with the address sanitizer, the leak sanitizer is included!
# SANITIZE_LEAK   : Set to YES to build with the leak sanitizer stand-alone. (deprecated)
# SANITIZE_THREAD : Set to YES to build with the trhead sanitizer.
# SANITIZE_UNDEF  : Set to YES to build with the undef sanitizer.
#   See : https://gcc.gnu.org/onlinedocs/gcc/Instrumentation-Options.html
#   - The thread sanitizer takes precedence and deactivates SANITIZE_ADDRESS and _LEAK due to
#     incompatibilities.
#   - The address sanitizer includes a more modern version of the old leak sanitizer and
#     deactivates SANITIZE_LEAK.
#   - The undef sanitizer is neutral to the others and can always be combined.
#   - See: scripts/Makefile.inc.Havi
# -------------------------------------------------------------------------------------------------
DEBUG            := $(if $(DEBUG),$(DEBUG),YES)
DEBUG_LOCK       := $(if $(DEBUG_LOCK),$(DEBUG_LOCK),NO)
JUST_PRINT       := $(if $(JUST_PRINT),$(JUST_PRINT),NO)
SANITIZE_ADDRESS := $(if $(SANITIZE_ADDRESS),$(SANITIZE_ADDRESS),NO)
SANITIZE_LEAK    := $(if $(SANITIZE_LEAK),$(SANITIZE_LEAK),NO)
SANITIZE_THREAD  := $(if $(SANITIZE_THREAD),$(SANITIZE_THREAD),NO)
SANITIZE_UNDEF   := $(if $(SANITIZE_UNDEF),$(SANITIZE_UNDEF),NO)
#
# If test is called, DEBUG must be yes, whether wanted or not. (The tests just don't make sense otherwise)
ifneq (,$(findstring test,$(MAKECMDGOALS)))
  DEBUG := YES
endif
#
#
# -------------------------------------------------------------------------------------------------
# Address and leak sanitizers can be combined, but are mutually exclusive to the thread sanitizer.
# The undefined sanitzer is neutral and works fine with either.
# See: # https://gcc.gnu.org/onlinedocs/gcc/Instrumentation-Options.html
# -------------------------------------------------------------------------------------------------
#
# List of all targets covered by special target 'full'
# -------------------------------------------------------------------------------------------------
ELMI_LIBS :=
ELMI_TEST :=
ELMI_TOOL := elomig
ELMI_EVERYTHING := $(ELMI_LIBS) $(ELMI_TEST) $(ELMI_TOOL)
#
# -------------------------------------------------------------------------------------------------
# Globale values that are used in many places
# -------------------------------------------------------------------------------------------------
PROJECT_DIR := ${CURDIR}
INCLUDE_DIR := $(PROJECT_DIR)/src
PREFIX      := $(if $(PREFIX),$(PREFIX),$(PROJECT_DIR)/install)
#
#
# -------------------------------------------------------------------------------------------------
# Set up the build environment
# -------------------------------------------------------------------------------------------------
caller_CFLAGS   := $(CFLAGS)
caller_CPPFLAGS := $(CPPFLAGS)
caller_CXXFLAGS := $(CXXFLAGS)
caller_LDFLAGS  := $(LDFLAGS)
CPPFLAGS := -I$(INCLUDE_DIR)
CFLAGS   :=
CXXFLAGS :=
LDFLAGS  :=
#
#
# -----------------------------------------------------------------------------
# Basic switches and locations
# -----------------------------------------------------------------------------
CMAKE_DIR        := $(PROJECT_DIR)/cmake-build
MAKE_OPT         := $(if $(MAKE_OPT),$(MAKE_OPT),)
NINJA_OPT        :=
#
#
# -----------------------------------------------------------------------------
# Tools to use
# The compiler can be overwritten with:
#   "make <options> CC=clang" (or other)
# -----------------------------------------------------------------------------
AR      := $(if $(AR),$(AR),$(shell which ar) r)
CC      := $(if $(CC),$(CC),$(shell which gcc))
CMAKE   := $(if $(CMAKE),$(CMAKE),$(shell which cmake))
CXX     := $(if $(CXX),$(CXX),$(shell which g++))
GCC     := $(if $(GCC),$(GCC),$(shell which gcc))
LN      := $(if $(LN),$(LN),$(shell which ln) -s)
MAKE    := $(if $(MAKE),$(MAKE),$(shell which make))
MKDIR   := $(if $(MKDIR),$(MKDIR),$(shell which mkdir) -p)
MV      := $(if $(MV),$(MV),$(shell which mv))
NINJA   := $(if $(NINJA),$(NINJA),$(shell which ninja))
OBJCOPY := $(if $(OBJCOPY),$(OBJCOPY),$(shell which objcopy))
RM      := $(if $(RM),$(RM),$(shell which rm) -f)
SED     := $(if $(SED),$(SED),$(shell which sed))
TOUCH   := $(if $(TOUCH),$(TOUCH),$(shell which touch))
# Use the compiler as the linker.
LD      := $(if $(LD),$(LD),$(CC))
#
#
# -----------------------------------------------------------------------------
# Default flags for both C++ and C
# -----------------------------------------------------------------------------
CMAKE_DO_INST     := 1
CMAKE_OPT         := --verbose
CMAKE_SANITIZE    := OFF
CMAKE_STRIP       := --strip
CMAKE_TARGET      := RelWithDebInfo
CMAKE_VERBOSE     := OFF
COMMON_FLAGS      := -Wall -Wextra -Wpedantic
GCC_CXXSTD        := c++17
GCC_STACKPROT     := -fstack-protector
MAKE_DO_STRIP     := 1
#
#
# -----------------------------------------------------------------------------
# Determine proper stack protector switch
# -----------------------------------------------------------------------------
ifeq (YES,$(DEBUG))
	GCC_STACKPROT := -fstack-protector-strong
endif
COMMON_FLAGS += ${GCC_STACKPROT}
#
#
# -----------------------------------------------------------------------------
# Determine which machine settings to use
# -----------------------------------------------------------------------------
MARCH := $(if $(MARCH),$(MARCH),-march=native)
#
#
# -----------------------------------------------------------------------------
# Make sure "--just-print" gets translated over to ninja and make calls
# -----------------------------------------------------------------------------
ifneq (,$(findstring n,$(MAKEFLAGS)))
	FILTER_ME = n
	override MAKEFLAGS    := $(filter-out $(FILTER_ME),$(MAKEFLAGS))
	override MAKEOVERRIDE := $(MAKEFLAGS)
	# Explicitly set JUST_PRINT to "YES"
	JUST_PRINT := YES
endif
#
# Simulate --just-print?
ifeq (YES,$(JUST_PRINT))
	CMAKE_DO_INST := 0
	CMAKE_OPT     :=
	DEBUG         := YES
	MAKE_OPT      := --just-print --print-directory --keep-going --always-make --jobs=1
	NINJA_OPT     := -v -j 1 -k 0 -t commands
endif
#
# Do not strip in DEBUG mode
ifeq (YES, ${DEBUG})
	MAKE_DO_STRIP := 0
endif
#
# Note: Add this to your main Makefile targets to utilize CMAKE_DO_INST:
#	test $(CMAKE_DO_INST) -eq 1 && $(CMAKE) \
#		-DCMAKE_BUILD_TYPE=$(CMAKE_TARGET) -DCOMPONENT=$@ \
#		-P "$(CMAKE_DIR)"/cmake_install.cmake $(CMAKE_STRIP) \
#		|| true
# ----------------------------------------------------------------------
#
# Note: Add this to your main Makefile targets to utilize MAKE_DO_STRIP.
#	$(OBJCOPY) --only-keep-debug $(@) $(@).debug
#	test $(MAKE_DO_STRIP) -eq 1 && \
#		$(OBJCOPY) --strip-all $(@) $(@).stripped \
#		|| \
#		$(OBJCOPY) --strip-debug $(@) $(@).stripped
#	$(MV) $(@).stripped $(@)
#	$(OBJCOPY) --add-gnu-debuglink=$(@).debug $(@)
# ----------------------------------------------------------------------
#
#
# -----------------------------------------------------------------------------
# Debug Mode settings
# @TODO : This must be fully ported to CMakeLists.txt so that only
#         `-DCMAKE_BUILD_TYPE`, `-DCMAKE_SANITIZE` and `-DSANITIZE_FLAGS` are
#         relevant to be set!
#         GOAL: Makefile must not set _ANY_ *FLAGS!
# -----------------------------------------------------------------------------
HAS_DEBUG_FLAG := NO
OBJ_SUB_DIR    := release
#
ifneq (,$(findstring -g,$(CFLAGS)))
	ifneq (,$(findstring -ggdb,$(CFLAGS)))
		HAS_DEBUG_FLAG := YES
	endif
	DEBUG := YES
endif
#
ifeq (NO,$(HAS_DEBUG_FLAG))
	# We always add gdb optimized debug symbols.
	# Release builds can get them stripped later.
	COMMON_FLAGS := -ggdb ${COMMON_FLAGS}
endif
#
ifeq (YES,$(DEBUG))
	CMAKE_SANITIZE :=
	CMAKE_STRIP    :=
	CMAKE_TARGET   := Debug
	CMAKE_VERBOSE  := ON
	COMMON_FLAGS   := ${MARCH} ${COMMON_FLAGS} -Og
	CPPFLAGS       += -D_DEBUG
	HAVE_SANITIZER := NO
	SANITIZE_FLAGS :=
	ifeq (NO,$(JUST_PRINT))
		MAKE_OPT  := --print-directory --keep-going
		NINJA_OPT := -v -j 1 -k 1
	endif
	# Thread sanitizer activiation first, it wins over address and leak
	ifeq (YES,$(SANITIZE_THREAD))
		# Note: If the thread sanitizer is used, Lockable has to utilize std::mutex.
		CMAKE_DIR        := ${CMAKE_DIR}-tsan
		CMAKE_SANITIZE   := thread
		SANITIZE_FLAGS   := -fsanitize=thread -fno-omit-frame-pointer -fno-common -static-libtsan
		HAVE_SANITIZER   := YES
		SANITIZE_ADDRESS := NO
		SANITIZE_LEAK    := NO
	endif
	# address sanitizer activition
	ifeq (YES,$(SANITIZE_ADDRESS))
		CMAKE_DIR       := ${CMAKE_DIR}-asan
		CMAKE_SANITIZE  := address
		SANITIZE_FLAGS  := -fsanitize=address -fno-omit-frame-pointer -fno-common -static-libasan
		HAVE_SANITIZER  := YES
		SANITIZE_LEAK   := NO
	endif
	# Leak detector activation
	ifeq (YES,$(SANITIZE_LEAK))
		CMAKE_DIR       := ${CMAKE_DIR}-lsan
		SANITIZE_FLAGS  := -fsanitize=leak -fno-omit-frame-pointer -fno-common -static-liblsan
		CMAKE_SANITIZE  := leak
		HAVE_SANITIZER  := YES
	endif
	# Undefined detector activation
	ifeq (YES,$(SANITIZE_UNDEF))
		CMAKE_DIR       := ${CMAKE_DIR}-undef
		SANITIZE_FLAGS  += -fsanitize=undefined -fno-sanitize=vptr -static-libubsan
		ifeq (YES,$(HAVE_SANITIZER))
			CMAKE_SANITIZE := ${CMAKE_SANITIZE},
		else
			SANITIZE_FLAGS += -fno-omit-frame-pointer -fno-common
		endif
		CMAKE_SANITIZE  := ${CMAKE_SANITIZE}undef
		HAVE_SANITIZER  := YES
	endif
	# Put objects in debug folder, if no sanitizer was selected
	ifeq (NO,$(HAVE_SANITIZER))
		CMAKE_SANITIZE := OFF
		CMAKE_DIR      := ${CMAKE_DIR}-debug
	endif
	# Utilize Sanatize flags if set
	ifeq (YES,$(HAVE_SANITIZER))
		COMMON_FLAGS += ${SANITIZE_FLAGS}
		LDFLAGS      += ${SANITIZE_FLAGS}
	endif
else
	COMMON_FLAGS := ${MARCH} ${COMMON_FLAGS} -O2
	CPPFLAGS     += -DNDEBUG
	CMAKE_DIR    := ${CMAKE_DIR}-release
	ifeq (NO,$(JUST_PRINT))
		NINJA_OPT := -v -j 8 -k 4
	endif
endif
#
#
# -----------------------------------------------------------------------------
# Finalize cmake config
# -----------------------------------------------------------------------------
CMAKE_CONF  := ${CMAKE_DIR}/build.ninja
CMAKE_STAMP := $(CMAKE_DIR)/.stamp
NINJA_DEST  := -C $(CMAKE_DIR)
#
#
# -----------------------------------------------------------------------------
# Finalize build management wrappers
# -----------------------------------------------------------------------------
ifneq (, ${MAKE_OPT})
	MAKE += ${MAKE_OPT}
endif
#
#
# -----------------------------------------------------------------------------
# Flags for compiler and linker
# -----------------------------------------------------------------------------
DEFINES  := -D_GNU_SOURCE
CPPFLAGS += -fPIC $(DEFINES)
CXXFLAGS := $(COMMON_FLAGS) -std=$(GCC_CXXSTD)
LDFLAGS  += -fPIE
ifeq (YES,$(HAVE_SANITIZER))
	CXXFLAGS += -static-libstdc++
endif
#
#
# -----------------------------------------------------------------------------
# Eventually append caller flags for overrides
# -----------------------------------------------------------------------------
CPPFLAGS := $(strip $(CPPFLAGS)) $(strip $(caller_CPPFLAGS))
CFLAGS   := $(strip $(CPPFLAGS)) $(strip $(CFLAGS)) $(strip $(caller_CFLAGS))
CXXFLAGS := $(strip $(CPPFLAGS)) $(strip $(CXXFLAGS)) $(strip $(caller_CXXFLAGS))
LDFLAGS  := $(strip $(LDFLAGS)) $(strip $(caller_LDFLAGS))
#
#
#
# -------------------------------------------------------------------------------------------------
#
.PHONY: all clean cleanandprint distclean doc full help justprint veryclean $(ELMI_EVERYTHING)

# -------------------------------------------------------------------------------------------------
# If no target was set, print the help text
# -------------------------------------------------------------------------------------------------
all:
	+@( test "$(JUST_PRINT)" = "YES" \
		&& $(MAKE) full JUST_PRINT=YES DEBUG=YES \
		|| $(MAKE) help \
	)


# -------------------------------------------------------------------------------------------------
# The help text - Please keep this current!
# -------------------------------------------------------------------------------------------------
help:
	@echo "The following targets are available:"
	@echo "----------------------------------------------------------------------"
	@echo "basic        : Build the basic  library libHaviBasic,  target lib_havi_basic"
	@echo "core         : Build the core   library libHaviCore,   target lib_havi_core"
	@echo "log          : Build the log    library libHaviLog,    target lib_havi_log"
	@echo "mem          : Build the mem    library libHaviMem,    target lib_havi_mem"
	@echo "thread       : Build the thread library libHaviThread, target lib_havi_thread"
	@echo "----------------------------------------------------------------------"
	@echo "clean        : Clean the corresponding build directory"
	@echo "cleanandprint: make clean ; make justprint"
	@echo "doc          : Build and install all documentation."
	@echo "distclean    : make veryclean and wipe the build directory"
	@echo "elomig       : Build elomig without the tests"
	@echo "full         : Build elomig and all tests"
	@echo "help         : Print this help"
	@echo "justprint    : make full with --justprint option"
	@echo "test         : Build the tests and run them"
	@echo "veryclean    : make clean and remove all components, tests and tools"
	@echo ""
	@echo "The following settings have been set:"
	@echo "----------------------------------------------------------------------"
	@echo "Debug Mode     : $(DEBUG)"
	@echo ""
	@echo "MAKE           : $(MAKE)"
	@echo "GCC            : $(GCC)"
	@echo "CC             : $(CC)"
	@echo "CXX            : $(CXX)"
	@echo "LD             : $(LD)"
	@echo ""
	@echo "CMAKE_DO_INST  : $(CMAKE_DO_INST)"
	@echo "CMAKE_DIR      : $(CMAKE_DIR)"
	@echo "CMAKE_SANITIZE : $(CMAKE_SANITIZE)"
	@echo "CMAKE_STAMP    : $(CMAKE_STAMP)"
	@echo "CMAKE_STRIP    : $(CMAKE_STRIP)"
	@echo "CMAKE_TARGET   : $(CMAKE_TARGET)"
	@echo "CMAKE_VERBOSE  : $(CMAKE_VERBOSE)"
	@echo ""
	@echo "MAKE_DO_STRIP  : $(MAKE_DO_STRIP)"
	@echo ""
	@echo "CPPFLAGS       : $(CPPFLAGS)"
	@echo "CFLAGS         : $(CFLAGS)"
	@echo "CXXFLAGS       : $(CXXFLAGS)"
	@echo "LDFLAGS        : $(LDFLAGS)"
	@echo "----------------------------------------------------------------------"


# -------------------------------------------------------------------------------------------------
# Regular Targets for the build system
# -------------------------------------------------------------------------------------------------
$(CMAKE_DIR):
	+$(MKDIR) "$(CMAKE_DIR)"


$(CMAKE_STAMP): $(CMAKE_DIR)
	+$(TOUCH) $@


$(CMAKE_CONF): Makefile CMakeLists.txt $(CMAKE_STAMP)
	@echo "Configuring $@"
	+( cd "$(CMAKE_DIR)" && \
		$(CMAKE)        \
		-DCMAKE_C_FLAGS_INIT="$(CFLAGS)"          \
		-DCMAKE_CXX_FLAGS_INIT="$(CXXFLAGS)"      \
		-DCMAKE_BUILD_TYPE=$(CMAKE_TARGET)        \
		-DCMAKE_SANITIZE=$(CMAKE_SANITIZE)        \
		-DCMAKE_VERBOSE_MAKEFILE=$(CMAKE_VERBOSE) \
		-DSANITIZE_FLAGS="$(SANITIZE_FLAGS)"      \
		-G Ninja $(PROJECT_DIR) -DCMAKE_INSTALL_PREFIX=$(PREFIX) )


clean:
	+@echo "[*] Performing clean..."
	+$(NINJA) $(NINJA_DEST) -t cleandead


cleanandprint: $(CMAKE_CONF)
	+($(MAKE) clean DEBUG=YES)
	+($(MAKE) full JUST_PRINT=YES DEBUG=YES)


distclean: veryclean
	+@echo "[*] Performing distclean..."
	+$(RM) -r $(CMAKE_DIR)


elomig: $(ELMI_TOOL)


full: $(ELMI_EVERYTHING)


justprint: $(CMAKE_CONF)
	+($(MAKE) full JUST_PRINT=YES DEBUG=YES)


test: $(ELMI_TEST)
	+@echo "Tests and running tests are not implemented, yet"


veryclean: clean
	+@echo "[*] Performing veryclean..."
	+$(NINJA) $(NINJA_DEST) -t clean


# -------------------------------------------------------------------------------------------------
# Named targets of the CMakeLists.txt with auto strip and install
# -------------------------------------------------------------------------------------------------
$(ELMI_EVERYTHING): $(CMAKE_CONF)
	+@( test "$(JUST_PRINT)" = "YES" && ( \
		echo "Printing $@ build steps ..." &&                  \
		echo "make[1]: Entering directory '$(PROJECT_DIR)'" && \
		$(NINJA) $(NINJA_DEST) $(NINJA_OPT) &&                 \
		echo "make[1]: Leaving directory '$(PROJECT_DIR)'"     \
	) || \
		echo "Building $@ ..." &&                       \
		$(CMAKE) --build "$(CMAKE_DIR)" --target $@ &&  \
		echo "$@ built" &&                              \
		test $(CMAKE_DO_INST) -eq 1 &&                  \
			echo -e "installing $@" &&                  \
			$(CMAKE) $(CMAKE_OPT)                       \
				-DCMAKE_BUILD_TYPE=$(CMAKE_TARGET) -DCOMPONENT=$@    \
				-P "$(CMAKE_DIR)"/cmake_install.cmake $(CMAKE_STRIP) \
		|| true )


doc: $(CMAKE_CONF)
	echo "Building $@ ..." &&                                    \
	$(CMAKE) --build "$(CMAKE_DIR)" --target documentation &&    \
	echo "$@ built" &&                                           \
	test $(CMAKE_DO_INST) -eq 1 &&                               \
		echo -e "installing $@" &&                               \
		$(CMAKE) $(CMAKE_OPT)                                    \
			-DCMAKE_BUILD_TYPE=$(CMAKE_TARGET) -DCOMPONENT=docs  \
			-P "$(CMAKE_DIR)"/cmake_install.cmake $(CMAKE_STRIP) \
	|| true


# -------------------------------------------------------------------------------------------------
.DEFAULT: all
