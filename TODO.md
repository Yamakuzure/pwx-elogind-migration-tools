# Migration Plan for elomig (Port of check_tree.pl & migrate_tree.pl)

## Overview

The `elomig` tool is a C++17 port of the Perl scripts `check_tree.pl` and `migrate_tree.pl`, which migrate systemd commits to
elogind.

The tool provides two main modes:

1. **checktree mode**: Compare systemd and elogind sources to detect changes and generate unified diffs.
2. **migrate mode**: Generate, refactor, and apply patches to migrate from systemd to elogind.

The goal of this plan is to guide coding agents through the remaining missing implementations until `elomig` fully reproduces
the behavior of both original Perl scripts.

## Terminology and Numbering

This plan uses a four-level hierarchy so coding agents and humans can refer to work items precisely.

- **Phase**: Top-level functional area.
  - Number format: `1.`, `2.`, `3.`
  - Example instruction: “Work on Phase 1.”

- **Work Package**: A coherent group of work inside a phase.
  - Number format: `1.1.`, `1.2.`, `2.7.`
  - Usually corresponds to one source file, class, or closely related feature area.
  - Example instruction: “Work on Work Package 2.7.”

- **Implementation Task**: A concrete coding task.
  - Number format: `1.1.1.`, `1.1.2.`, `2.7.1.`
  - Should normally fit into one focused coding session.
  - Example instruction: “Work on Implementation Task 2.7.1.”

- **Action Item**: A fine-grained checklist item inside an Implementation Task.
  - Number format: `1.1.1.1.`, `1.1.1.2.`, `2.7.1.3.`
  - Example instruction: “Work on Action Item 2.7.1.3.”

## Completion Rules

- Mark an item as complete by changing `[ ]` to `[x]`.
- A parent item should only be marked complete when all child items below it are complete.
- An Implementation Task should only be marked complete after:
  - The relevant code is implemented.
  - Existing behavior is preserved.
  - The project builds successfully.
  - Relevant tests are added or updated where practical.
  - Behavior is checked against the original Perl implementation where applicable.
- If an agent discovers that an item is too large, it should split it into smaller child items before implementing it.
- If the Perl behavior is unclear, document the ambiguity in this file before implementing.

## Phases


## Additional Notes

- Follow existing project style and architecture.
- Use C++17.
- Prefer RAII, smart pointers, standard library containers, and explicit error handling.
- Avoid inventing behavior where the Perl scripts define existing behavior.
- When the Perl behavior is unclear, document the ambiguity in this file before implementing.
- Preserve command-line compatibility where possible.
- Prefer small, reviewable changes that complete one Implementation Task or Action Item at a time.
- Do not mark parent items complete until all child items are complete.

## Feature-Complete Checklist


## Detected Issues


## Needed Enhancements

