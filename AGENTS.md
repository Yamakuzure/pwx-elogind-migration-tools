---
apply: always
---

# AGENTS.md - Agentic Coding Guidelines for the EdenWorX elogind migration tools

This file provides comprehensive guidelines for agentic coding agents working on the EdenWorX elogind migration tools.

- **NEVER** spawn background agents for parallel work!
- **ALWAYS** process files sequentially!
- **ALWAYS** explain what your current step or task is!

## Project Overview

Tools to migrate systemd commits to elogind. Put into their own repo to make them branch agnostic.

### Important Programs

- `check_tree.pl` : Creates a unified diff on a file or all files in `./src` and updates the resulting patches for elogind.
- `cleanup_headers.sh` : Searches and lists headers that are nowhere included.
- `find_orphans.pl` : Searches and lists files that are ignored by the meson build system of elogind.
- `migrate_tree.pl` : Searches relevant commits in a systemd checkout, and uses `check_tree.pl` on each to port it to elogind.
- `update_po_files.pl` : Masks all entries in `po` files that are for files which are not used by elogind.

**Only** `check_tree.pl` can be effectively tested here, as the other programs must be called from an actual elogind checkout.

## Build Commands

These tools are written in Perl and do not need to be built.

## Lint Commands

### Perl Scripts
```bash
# Perltidy (formatting)
perltidy [files.pl]           # Uses .perltidyrc config

# Perl::Critic (static analysis)
perlcritic [files.pl]         # Uses .perlcriticrc, severity=1
```

### C Code
```bash
# Clang-format (formatting)
clang-format -i [files.c]     # Uses .clang-format, requires v19+
```

### Shell Scripts
```bash
# ShellCheck (if available)
shellcheck [scripts.sh]
```

## Test Commands

### Running Single Tests
```bash
# Individual Perl scripts (syntax check)
perl -c check_tree.pl
perl -c find_orphans.pl
perl -c migrate_tree.pl
perl -c update_po_files.pl

# Run with --help to verify execution
./check_tree.pl --help
./find_orphans.pl --help
./migrate_tree.pl --help
```

### Manual Testing
All programs operate on systemd/elogind source trees.
The only program that we can test from within this directory is `check_tree.pl`.
- Test files from elogind are in `./src/` ; manually added by the user.
- Test files from systemd are in `./systemd` ; manually added by the user.
- Ask user to copy files that are missing, before performing tests.
- Patches are built in `./patches/`
- Verify patches apply cleanly with `git apply --check`

Command to test `check_tree.pl`:
```bash
# <filename> is a relatife path, e.g. src/shared/cgroup-setup.c
./check_tree.pl --debug --upstream ./systemd --file <filename>
```

## Code Style Guidelines

### General Conventions
- **Line Length**: Maximum 168 columns (both C and Perl)
- **Line Endings**: Unix-style LF only
- **Encoding**: ASCII/UTF-8 (Perl: `enc=none`)
- **Indentation**: 8 spaces (no tabs for alignment)

### C Code Style
- **Braces**: Required for all control structures (`InsertBraces: true`)
- **Brace Style**: K&R style (break before braces: Custom)
- **Pointer Alignment**: Left (`int *ptr`)
- **Qualifiers**: Right-aligned (`const int`)
- **Spaces**:
  - Before assignment operators: yes
  - In parentheses: conditional statements yes, empty no
  - Before case colon: no
  - After C-style cast: no
- **Namespace Indentation**: Inner namespaces indented
- **Includes**: Sorted case-sensitively, regrouped by category
  1. Local headers ("*.h")
  2. Havilib headers
  3. Image format headers
  4. Test libraries (gtest, gmock, isl, json)
  5. System headers (<...>)
- **Integer Literals**: Decimal separator every 3 digits (4+ digits)
- **Trailing Semicolons**: Removed where possible
- **Empty Lines**: Max 2 consecutive, keep at start of blocks

### Perl Code Style
- **Pragmas**: Always use `strict` and `warnings FATAL => 'all'`
- **Error Handling**: Use Carp, Try::Tiny, Readonly
- **Variable Declarations**: My with explicit scoping
- **Subroutine Prototypes**: Avoid unless necessary
- **Documentation**: POD format required
- **Naming**:
  - Variables: lowercase with underscores (`$my_var`)
  - Subroutines: lowercase with underscores (`sub my_function`)
  - Constants: UPPERCASE with `Readonly`
- **Control Structures**:
  - Braces optional for single statements (perltidy: `-ce`)
  - Continuation indentation: 8 spaces
- **Comments**: English language, descriptive
- **Maximum Arguments**: 6 per subroutine
- **Regex**: Extended formatting required for 16+ characters
- **McCabe Complexity**: Max 30 for main subroutines

### Shell Script Style
- **Shebang**: `#!/bin/bash`
- **Quoting**: Always quote variables: `"$var"`
- **Conditionals**: Use `[[ ]]` not `[ ]`
- **Functions**: Use `function name()` or `name()` consistently
- **Exit Codes**: Return meaningful exit codes (0=success)
- **Error Handling**: Use `set -x` for debugging, `set -e` with care

### Import/Include Organization
- Group by type (local, third-party, system)
- Alphabetical within groups
- One include per line
- No unused includes

### Error Handling
- **C**: Check all syscalls, use goto fail pattern for cleanup
- **Perl**: Use Try::Tiny, localized punctuation vars allowed: `$@`, `$!`, `$?`, `$$`, `$|`
- **Shell**: Check command return values, provide helpful error messages

### Naming Conventions
- **Files**: lowercase with underscores or dashes
- **Functions**: Descriptive, action-oriented names
- **Variables**: Clear purpose, avoid abbreviations except well-known ones
- **Constants**: UPPERCASE (Perl), kConstantName or CONSTANT (C)

### Documentation Requirements
- **Perl**: POD documentation with VERSION, HISTORY sections
- **C**: Doxygen-style comments for public APIs
- **Shell**: Header comments with purpose and usage
- **Patches**: Clear commit messages, reference issues

### Git Workflow
- Commit messages: Clear, descriptive
- Patches: Apply cleanly, test before committing
- Branch strategy: Feature branches, main for stable

### Special Project Conventions
- Mask blocks: `#if 0 // elogind` / `#else // 0` / `#endif // 0`
- Insert blocks: `#if 1 // elogind` / `#endif // 1`
- Name changes: systemd <-> elogind handled carefully
- GLIBC compatibility: `__GLIBC__` masks for musl support
- XML files: Special handling for policy.in files
- Shell mask/unmask: Track for proper patch generation
