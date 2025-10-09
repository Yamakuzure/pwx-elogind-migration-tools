#!/usr/bin/perl -w
use strict;
use warnings FATAL => 'all';

use Carp;
use Cwd     qw( getcwd abs_path );
use English qw( -no_match_vars );
use File::Basename;
use File::Find;
use Getopt::Long;
use Git::Wrapper;
use List::Util qw( first );
use Pod::Usage;
use Readonly;
use Try::Tiny;

# ================================================================
# ===        ==> --------     HISTORY      -------- <==        ===
# ================================================================
#
# Version  Date        Maintainer      Changes, Additions, Fixes
# 0.0.1    2017-04-08  sed, PrydeWorX  First basic design
# ... a lot of undocumented and partly lost development ...
# 0.8.0    2018-02-23  sed, PrydeWorX  2nd gen rewritten due to loss of the original thanks to stupidity.
# 0.8.1    2018-03-05  sed, PrydeWorX  Fixed all outstanding issues and optimized rewriting of shell files.
# 0.8.2    2018-03-06  sed, PrydeWorX  Added checks for elogind_*() function call removals.
# 0.8.3    2018-03-08  sed, PrydeWorX  Handle systemd-logind <=> elogind renames. Do not allow moving of
#                                        commented out includes under out elogind block.
# 0.8.4    2018-03-09  sed, PrydeWorX  Added handling of .gperf and .xml files.
# 0.8.5    2018-03-13  sed, PrydeWorX  Added possibility to (manually) check root files and enhanced the
#                                        handling of shell masks and unmasks.
# 0.8.6    2018-03-16  sed, PrydeWorX  Enhanced mask block handling and added handling of .sym files.
# 0.8.7    2018-04-20  sed, PrydeWorX  Add [un]preparation for XML files.
# 0.8.8    2018-05-08  sed, PrydeWorX  Use Git::Wrapper to checkout the wanted commit in the upstream tree.
# 0.8.9    2018-05-09  sed, PrydeWorX  Add new option --create to create non-existing files. Needs --file.
#                                      + Add new option --stay to to not reset back from --commit.
# 0.9.0    2018-05-15  sed, PrydeWorX  Do not prefix mask block content in XML file patch hunks with a '# '.
# 0.9.1    2018-05-17  sed, PrydeWorX  Replace the source in creation patches with /dev/null.
#                                      + Remember mask starts and elses in hunks, so the resulting patches
#                                        can be reworked without ignoring changes in useless hunks.
# 0.9.2    2018-05-24  sed, PrydeWorX  Enhance the final processing of shell and xml files and their patches
#                                        by remembering mask changes that get pruned from the hunks.
# 0.9.3    2018-05-25  sed, PrydeWorX  Made check_musl() and check_name_reverts() safer. Further policy.in
#                                        consist of XML code, and are now handled by (un)prepare_xml().
# 0.9.4    2018-05-29  sed, PrydeWorX  Fixed a bug that caused #else to not be unremoved in __GLIBC__ blocks.
#                                      + The word "systemd" is no longer changed to "elogind", if it was
#                                        found in a comment block that is added by the patch.
#                                      + Added missing detection of mask else switches in prune_hunk().
#                                      + Move move upstream appends from after our mask blocks up before
#                                        found #else switches.
# 0.9.5    2018-05-30  sed, PrydeWorX  Do not allow diff to move name reverts into a mask block.
#                                      + Do not replace double dashes in XML comments, that are either the
#                                        comment start or end.
# 0.9.6    2018-06-06  sed, PrydeWorX  Prune changes that change nothing. This eliminates some useless hunks.
# 0.9.7    2018-06-21  sed, PrydeWorX  Includes masked by C90 conformant /**/ are now handled as well.
# 0.9.8    2018-08-14  sed, PrydeWorX  Let .m4 files be prepared/unprepared, too.
# 0.9.9    2018-11-23  sed, PrydeWorX  Fix check_name_reverts() to no longer double lines, and allow to "fix"
#                                        name changes we did in mask blocks.
# 0.9.10   2019-01-18  sed, PrydeWorX  Make sure that empty commented lines do not get trailing spaces in
#                                        shell files.
# 0.9.11   2019-01-28  sed, PrydeWorX  Do not include trailing spaces in empty comment lines in patches for
#                                        shell files.
# 0.9.12   2019-02-20  sed, PrydeWorX  Do not leave an undef hunk in $hFile{hunks}, report and ignore.
#                                      + Issue #1/#4: Move additions right after mask endings up into the mask.
#                                      + Issue #2: Protect src/login/logind.conf.in
#                                      + Issue #3: Do not consider files in man/rules/
# 1.0.0    2019-03-19  sed, PrydeWorX  Allow __GLIBC__ to be a mask/insert start/end keyword to make musl-libc
#                                        compatibility easier to accomplish.
# 1.0.1    2019-09-30  sed, PrydeWorX  Don't assume __GLIBC__ preprocessor masks to be regular masks, as they
#                                        are already handled in check_musl().
# 1.0.2    2019-10-01  sed, PrydeWorX  Completely handle __GLIBC__ masks/inserts in check_musl()
# 1.1.0    2019-10-02  sed, PrydeWorX  Add check_empty_masks() to detect masks that became empty
# 1.2.0    2019-10-11  sed, PrydeWorX  Fixed check_empty_masks() to eliminate false positives and rewrote
#                                        check_useless() so it can catch useless blocks, too.
# 1.2.1    2020-01-23  sed, PrydeWorX  Fixed a bug that caused large removals to be undone if they started
#                                        right after additional includes for elogind. Further improved
#                                        check_masks() greatly!
# 1.2.2    2020-01-31  sed, PrydeWorX  Do the checking whether shell/xml preparations are needed a bit more
#                                        sophisticated and effectively.
# 1.3.0    2020-02-06  sed, PrydeWorX  From now on mask elses must be "#else // 0" to be recognized.
# 1.3.1    2020-08-18  sed, PrydeWorX  As this is easy to get wrong, elogind include additions can be be marked
#                                        with "needed for elogind", too.
# 1.3.2    2021-03-02  sed, PrydeWorX  Add LINGUAS to the list of shell files, as elogind has additional locales now.
# 1.4.0    2023-05-12  sed, EdenWorX   Fix accidental renaming of systemd-only apps and revert reversals into mask blocks.
# 1.4.1    2023-12-28  sed, EdenWorX   Do not revert a name change if the reversal moves the line into a mask.
#                                        Also check for reversals where the removal is anywhere before the addition. This fixes
#                                        multiline-comments to magically multiply when patches are applied by migrate_tree.pl..
# 1.4.2    2024-02-03  sed, EdenWorX   Do not migrate NEWS and TODO. They are elogind files now
# 1.4.3    2025-09-27  sed, EdenWorX   The name change (systemd<=>elogind) analysis and handling was completely overhauled,
#                                        and can correctly identify and handle changes over several lines.
#
# ========================
# === Little TODO list ===
# ========================
#
# ...nothing right now...
#
# ------------------------
## Please keep this current!
Readonly our $VERSION => '1.4.3';

# ---------------------------------------------------------
# Shared Variables
# ---------------------------------------------------------
# signal handling
my $death_note = 0;

# Global return value, is set to 1 by log_error()
my $ret_global = 0;

# ================================================================
# ===        ==> ------ Help Text and Version ----- <==        ===
# ================================================================
Readonly my $PROGDIR => dirname(__FILE__);
Readonly my $WORKDIR => getcwd();

# ================================================================
# ===        ==> ------ Constants and Helpers ----- <==        ===
# ================================================================
Readonly my $AT             => q{@};
Readonly my $ATAT           => q{@@}; ## no critic(ValuesAndExpressions::RequireInterpolationOfMetachars)
Readonly my $DASH           => q{-};
Readonly my $DOT            => q{.};
Readonly my $EMPTY          => q{};
Readonly my $FALSE          => 0;
Readonly my $HASH           => q{#};
Readonly my $KIND_ELOGIND   => 1;
Readonly my $KIND_LOGINCTL  => 2;
Readonly my $KIND_SYSTEMCTL => 4;
Readonly my $KIND_SYSTEMD   => 3;
Readonly my $PLUS           => q{+};
Readonly my $QUOT           => q{"};
Readonly my $SLASH          => q{/};
Readonly my $SPACE          => q{ };
Readonly my $STAR           => q{*};
Readonly my $TRUE           => 1;
Readonly my $TYPE_ADDITION  => 1;
Readonly my $TYPE_NEUTRAL   => 0;
Readonly my $TYPE_REMOVAL   => -1;

# ================================================================
# ===        ==> ------- Logging facilities ------- <==        ===
# ================================================================
my $do_debug          = 0;
my $have_progress_msg = 0;
my $logfile           = $EMPTY;

Readonly my $LOG_DEBUG   => 1;
Readonly my $LOG_INFO    => 2;
Readonly my $LOG_STATUS  => 3;
Readonly my $LOG_WARNING => 4;
Readonly my $LOG_ERROR   => 5;

# ================================================================
#===        ==> --------- Signal Handlers --------- <==        ===
# ================================================================
Readonly my %SIGS_CAUGHT => ( 'INT' => 1, 'QUIT' => 1, 'TERM' => 1 );
local $SIG{INT}  = \&sigHandler;
local $SIG{QUIT} = \&sigHandler;
local $SIG{TERM} = \&sigHandler;

# Warnings should be logged, too:
$SIG{__WARN__} = \&warnHandler;

# And fatal errors go to the log as well
$SIG{__DIE__} = \&dieHandler;

# ================================================================
# ===       ==> -------- File name patterns -------- <==       ===
# ================================================================
Readonly my %FILE_NAME_PATTERNS => (
	'shell' => [
		'LINGUAS',           'Makefile',    'meson', '\.gitignore$', '\.gperf$', '\.in$',       '\.m4$',         '\.pl$',
		'\.po$',             '\.pot$',      '\.py$', '\.sh$',        '\.sym$',   'bash/busctl', 'bash/loginctl', 'pam.d/other',
		'pam.d/system-auth', 'zsh/_busctl', 'zsh/_loginctl'
	],
	'xml' => [ '\.xml$', '\.ent\.in$', '\.policy\.in$/' ] ## no critic(ValuesAndExpressions::RequireInterpolationOfMetachars)
);

# And some protected website URLs
Readonly my %SYSTEMD_URLS => (
	'fedoraproject.org/projects/systemd' => 1,
	'freedesktop.org/software/systemd'   => 1
);

# ================================================================
# ===        ==> -------- Global variables -------- <==        ===
# ================================================================
my $do_create       = 0;       # If set to 1, a non-existing file is created.
my $do_stay         = 0;       # If set to 1, the previous commit isn't restored on exit.
my $file_fmt        = $EMPTY;  # Format string built from the longest file name in generate_file_list().
my $have_wanted     = 0;       # Helper for finding relevant files (see wanted())
my %hToCreate       = ();      # The keys are files that do not exist and shall be created.
my %hWanted         = ();      # Helper hash for finding relevant files (see wanted())
my $in_else_block   = 0;       # Set to 1 if we switched from mask/unmask to 'else'.
my $in_glibc_block  = 0;       # Set to 1 if we enter a __GLIBC__ block
my $in_mask_block   = 0;       # Set to 1 if we entered an elogind mask block
my $in_insert_block = 0;       # Set to 1 if we entered an elogind addition block
my @only_here       = ();      # List of files that do not exist in $upstream_path.
my $previous_commit = $EMPTY;  # Store current upstream state, so we can revert afterwards.
my $show_help       = 0;
my @source_files    = ();      # Final file list to process, generated in in generate_file_list().
my $upstream_path   = $EMPTY;
my $wanted_commit   = $EMPTY;
my @wanted_files    = ();      # User given file list (if any) to limit generate_file_list()

# ================================================================
# ===        ==> ------- MAIN DATA STRUCTURES ------ <==       ===
# ================================================================

## @brief %hFile is used globally for each file that is processed.
# The structure is:
# ( count  : Number of hunks stored
#   create : Set to 1 if this is a new file to be created, 0 otherwise.
#   hunks  : Arrayref with the Hunks, stored in %hHunk instances
#   is_sh  : 1 if the file name has a known shell pattern
#   is_xml : 1 if the file name has a known xml pattern
#   output : Arrayref with the lines of the final patch
#   part   : local relative file path
#   patch  : PROGDIR/patches/<part>.patch (With / replaced by _ in <part>)
#   pwxfile: Set to 1 if it is a prepared shell/xml file (See prepare_[shell,xml]())
#   source : WORKDIR/<part>
#   target : UPSTREAM/<part>
# )
my %hFile = (); ## Main data structure to manage a complete compare of two files. (See: build_hFile() )

## @brief $hHunk is used globally for each Hunk that is processed and points to the current $hFile{hunks}[] instance.
# The structure is:
# { count        : Number of lines in {lines}
#   idx          : Index of this hunk in %hFile{hunks}
#   lines        : list of the lines themselves.
#   masked_end   : 1 if this hunk ends in a masked block.
#   masked_start : 1 if the previous hunk ends in a masked block.
#   src_start    : line number this hunk starts in the source file.
#   tgt_start    : line number this hunk becomes in the target file.
#   useful       : 1 if the hunk is transported, 0 if it is to be omitted.
# }
my $hHunk = {}; ## Secondary data structure to describe one diff hunk.            (See: build_hHunk() )

## @brief: Only counted in the first step, actions are only in the second step.
# The structure is:
# { include => {
#     applied : Set to 1 once check_includes() has applied any rules on it.
#     elogind = { hunkid : Hunk id ; Position where a "needed by elogin" include is
#                 lineid : Line id ; wanted to be removed by the patch.
#     }
#     insert  = { elogind : Set to 1 if the insert was found under elogind special includes.
#                 hunkid  : Hunk id ; Position where a commented out include is
#                 lineid  : Line id ; wanted to be removed by the patch.
#                 spliceme: Set to 1 if this insert is later to be spliced.
#                 sysinc  : Set to 1 if it is <include>, 0 otherwise.
#     }
#     remove  = { hunkid : Hunk id ; Position where a new include is wanted to be
#                 lineid : Line id ; added by the patch.
#                 sysinc : Set to 1 if it is <include>, 0 otherwise.
#     }
# } }
my %hIncs = (); ## Hash for remembered includes over different hunks.

my %hProtected = (); ## check_name_reverts() notes down lines here, which check_comments() shall not touch

## @brief List of failed hunks.
# These are worth noting down in an extra structure, as these mean that something is fishy about a file,
# like elogind mask starts within masks.
# The structure is:
# ( { hunk : the failed hunk for later printing
#     msg  : a message set by the function that failed
#     part : local relative file part
#   }
# )
my @lFails = ();

# ================================================================
# ===        ==> --------  Function list   -------- <==        ===
# ================================================================
sub build_hFile;         # Initializes and fills %hFile.
sub build_hHunk;         # Adds a new $hFile{hunks}[] instance.
sub build_output;        # Writes $hFile{output} from all useful $hFile{hunks}.
sub check_blanks;        # Check that useful blank line additions aren't misplaced.
sub check_comments;      # Check comments we added for elogind specific information.
sub check_debug;         # Check for debug constructs
sub check_empty_masks;   # Check for empty mask blocks, remove them and leave a note.
sub check_func_removes;  # Check for attempts to remove elogind_*() special function calls.
sub check_includes;      # performe necessary actions with the help of %hIncs (built by read_includes())
sub check_masks;         # Check for elogind preprocessor masks
sub check_musl;          # Check for musl_libc compatibility blocks
sub check_name_reverts;  # Check for attempts to revert 'elogind' to 'systemd'
sub check_stdc_version;  # Check for removal of a dfined(__STDC_VERSION) guard
sub check_sym_lines;     # Check for attempts to uncomment unsupported API functions in .sym files.
sub check_useless;       # Check for useless updates that do nothing.
sub checkout_upstream;   # Checkout the given refid on $upstream_path
sub clean_hFile;         # Completely clean up the current %hFile data structure.
sub diff_hFile;          # Generates the diff and builds $hFile{hunks} if needed.
sub get_hunk_head;       # Generate the "@@ -xx,n +yy,m @@" hunk header line out of $hHunk.
sub hunk_failed;         # Generates a new @lFails entry and terminates the progress line.
sub hunk_is_useful;      # Prunes the hunk and checks whether it stil does anything
sub is_insert_end;       # Return 1 if the argument consists of any insertion end
sub is_insert_start;     # Return 1 if the argument consists of any insertion start
sub is_mask_else;        # Return 1 if the argument consists of any mask else
sub is_mask_end;         # Return 1 if the argument consists of any mask end
sub is_mask_start;       # Return 1 if the argument consists of any mask start
sub prepare_shell;       # Prepare shell (and meson) files for our processing
sub prepare_xml;         # Prepare XML files for our processing (Unmask double dashes in comments)
sub protect_config;      # Special function to not let diff add unwanted or remove our lines in logind.conf.in
sub prune_hunk;          # remove unneeded prefix and postfix lines.
sub read_includes;       # map include changes
sub splice_includes;     # Splice all includes that were marked for splicing
sub unprepare_shell;     # Unprepare shell (and meson) files after our processing
sub unprepare_xml;       # Unprepare XML files after our processing (Mask double dashes in comments)

# ================================================================
# ===     ==> -------    Argument handling     ------- <==     ===
# ================================================================
my $podmsg          = "\telogind git tree checker\n";
my %program_options = (
	'help|h+'      => \$show_help,
	'debug'        => \$do_debug,
	'commit|c=s'   => \$wanted_commit,
	'create'       => \$do_create,
	'file|f=s'     => \@wanted_files,
	'stay'         => \$do_stay,
	'upstream|u=s' => \$upstream_path
);
GetOptions(%program_options) or pod2usage( { -message => $podmsg, -exitval => 2, -verbose => 0 } );
$show_help > 1 and pod2usage( { -exitval => 0, -verbose => 2, -noperldoc => 0 } );
$show_help > 0 and pod2usage( { -exitval => 0, -verbose => 1, -noperldoc => 1 } );
( 0 < ( length $upstream_path ) ) or pod2usage( { -exitval => 1, -verbose => 0, -noperldoc => 1 } );

# ================================================================
# ===        ==> --------    Prechecks     -------- <==        ===
# ================================================================

do_prechecks() or pod2usage( { -exitval => 3, -verbose => 2, -noperldoc => 1 } );
set_log_file( basename($upstream_path) );
log_status('Program Start');
if ( ( length $wanted_commit ) > 0 ) {
	checkout_upstream($wanted_commit) ## Note: Does nothing if $wanted_commit is already checked out.
	        or exit 1;
}
generate_file_list() or exit 1; ## Note: @wanted_files is heeded.

# ================================================================
# ===        ==> -------- = MAIN PROGRAM = -------- <==        ===
# ================================================================

for my $file_part (@source_files) {

	# Pre-exit, check for a signal.
	( $death_note > 0 ) and next; ## No display, we already have the cancellation msg out!

	# Otherise begin with a progress show
	show_progress( 0, "$file_fmt: ", $file_part );

	# early exits
	build_hFile($file_part) or show_progress( 1, "$file_fmt: only here", $file_part ) and next;
	diff_hFile()            or show_progress( 1, "$file_fmt: same",      $file_part ) and next;

	# Reset global state helpers
	$in_else_block   = 0;
	$in_glibc_block  = 0;
	$in_mask_block   = 0;
	$in_insert_block = 0;

	# empty the include manipulation hash
	%hIncs = ();

	# ---------------------------------------------------------------------
	# --- Go through all hunks and check them against our various rules ---
	# ---------------------------------------------------------------------
	refactor_hunks();

	# Break off if a signal was caught
	( $death_note > 0 ) and show_progress( 1, "$file_fmt : cancelled", $file_part ) and next;

	# ---------------------------------------------------------------------
	# --- Make sure saved include data is sane                          ---
	# ---------------------------------------------------------------------
	include_check_sanity();

	# ---------------------------------------------------------------------
	# --- Go through all hunks and apply remaining changes and checks   ---
	# ---------------------------------------------------------------------
	finish_hunks();

	# ---------------------------------------------------------------------
	# --- Splice all include insertions that are marked for splicing    ---
	# ---------------------------------------------------------------------
	splice_includes();

	# ---------------------------------------------------------------------
	# --- Go through all hunks for a last prune and check               ---
	# ---------------------------------------------------------------------
	my $have_hunk = count_useful_hunks();

	# If we have at least 1 useful hunk, create the output and tell the user what we've got.
	( $have_hunk > 0 )
	        and build_output()  # (Always returns 1)
	        and show_progress( 1, "$file_fmt: %d Hunk%s", $file_part, $have_hunk, $have_hunk > 1 ? 's' : $EMPTY )
	        or show_progress( 1, "$file_fmt: clean", $file_part );

	# Shell and xml files must be unprepared. See unprepare_[shell,xml]()
	$hFile{pwxfile} and ( unprepare_shell() or unprepare_xml() );

	# Now write the patch if we have at least one hunk to write
	( $have_hunk > 0 ) and write_to_patch();
} ## end for my $file_part (@source_files)

# ===========================
# === END OF MAIN PROGRAM ===
# ===========================

# ================================================================
# ===        ==> --------     Cleanup      -------- <==        ===
# ================================================================

END {
	# -------------------------------------------------------------------------
	# --- Print out the list of files that only exist here and not upstream ---
	# -------------------------------------------------------------------------
	my $count = scalar @only_here;
	if ( $count > 0 ) {
		my $fmt = sprintf '%%%dd: %%s', ( length "$count" );

		log_status( "\n\t%d file%s only found in $WORKDIR:", $count, $count > 1 ? 's' : $EMPTY );

		for my $i ( 0 .. $count - 1 ) {
			log_status( $fmt, $i + 1, $only_here[$i] );
		}
	} ## end if ( $count > 0 )

	# -------------------------------------------------------------------------
	# --- Print out the list of failed hunks -> bug in hunk or program?     ---
	# -------------------------------------------------------------------------
	$count = scalar @lFails;
	if ( $count > 0 ) {

		log_warning( "\n%d file%s %s at least one fishy hunk:", $count, $count > 1 ? 's' : $EMPTY, $count > 1 ? 'have' : 'has' );

		for my $i ( 0 .. $count - 1 ) {
			log_warning("=== $lFails[$i]{part} ===");
			log_warning(" => $lFails[$i]{msg} <=");
			log_warning('---------------------------');
			log_warning( " {count}        : ${QUOT}" . $lFails[$i]{info}{count} . $QUOT );
			log_warning( " {idx}          : ${QUOT}" . $lFails[$i]{info}{idx} . $QUOT );
			log_warning( " {masked_end}   : ${QUOT}" . $lFails[$i]{info}{masked_end} . $QUOT );
			log_warning( " {masked_start} : ${QUOT}" . $lFails[$i]{info}{masked_start} . $QUOT );
			log_warning( " {offset}       : ${QUOT}" . $lFails[$i]{info}{offset} . $QUOT );
			log_warning( " {src_start}    : ${QUOT}" . $lFails[$i]{info}{src_start} . $QUOT );
			log_warning( " {tgt_start}    : ${QUOT}" . $lFails[$i]{info}{tgt_start} . $QUOT );
			log_warning( " {useful}       : ${QUOT}" . $lFails[$i]{info}{useful} . $QUOT );
			log_warning('---------------------------');
			foreach ( @{ $lFails[$i]{hunk} } ) { log_warning("$_") }
		} ## end for my $i ( 0 .. $count...)
	} ## end if ( $count > 0 )

	$do_stay or ( length $previous_commit ) and checkout_upstream($previous_commit);

	log_status('Program End');
} ## end END

# ================================================================
# ===        ==> ---- Function Implementations ---- <==        ===
# ================================================================

## @brief Builds the hFile data structure for a given part.
#
#  This subroutine initializes the %hFile hash with information about the file being processed,
#  including its source, target, patch location, and whether it's a shell or XML file requiring special handling.
#  It also checks if the target file exists and adds the part to @only_here if it doesn't.
#
#  @param part The name of the part/file to process.
#  @return Returns 1 on success, 0 if the target file does not exist.
sub build_hFile {
	my ($part) = @_;

	( defined $part ) and ( length $part ) or log_error('ERROR') and confess('build_hfile: part is empty ???');

	# Is this a new file?
	my $isNew = ( defined $hToCreate{$part} ) ? 1 : 0;

	# We only prefixed './' to unify things. Now it is no longer needed:
	$part =~ s/^[${DOT}][${SLASH}]//msx;

	# Pre: erase current $hFile, as that is what is expected.
	clean_hFile();

	# Check the target file
	my $tgt = "$upstream_path/$part";
	$tgt =~ s/elogind/systemd/msg;
	$tgt =~ s/[${DOT}]pwx$//ms;
	-f $tgt
	        or ( push @only_here, $part )
	        and return 0;

	# Build the patch name
	my $patch = $part;
	$patch =~ s/\//_/msg;

	# Determine whether this is a shell or xml file needing preparations.
	my $is_sh  = 0;
	my $is_xml = 0;
	for my $pat ( @{ $FILE_NAME_PATTERNS{'xml'} } ) {
		$part =~ m/$pat/ms and $is_xml = 1 and last;
	}
	if ( 0 == $is_xml ) {
		for my $pat ( @{ $FILE_NAME_PATTERNS{'shell'} } ) {
			$part =~ m/$pat/msx and $is_sh = 1 and last;
		}
	}

	# Build the central data structure.
	%hFile = (
		count   => 0,
		create  => $isNew,
		hunks   => [],
		is_sh   => $is_sh,
		is_xml  => $is_xml,
		output  => [],
		part    => "$part",
		patch   => "$PROGDIR/patches/${patch}.patch",
		pwxfile => 0,
		source  => "$WORKDIR/$part",
		target  => "$tgt"
	);

	return 1;
} ## end sub build_hFile

## @brief Builds a hunk object from header and lines data.
#
#  This subroutine processes the header line of a hunk to extract source and target
#  starting line numbers. It then stores the hunk's lines, updating the internal
#  hunk counter and structure. If the header format is invalid, it logs an error
#  and returns false.
#
#  @return Returns 1 on successful hunk creation, 0 otherwise.
sub build_hHunk {
	my ( $head, @lHunk ) = @_;
	my $pos  = $hFile{count}++;
	my $mark = qq<[${AT}]{2}>;

	# The first line must be the hunk positional and size data.
	# example: @@ -136,6 +136,8 @@
	# That is @@ -<source line>,<source length> +<target line>,<target length> @@
	if ( $head =~ m/^${mark}\s+-(\d+),\d+\s+[${PLUS}](\d+),\d+\s+${mark}/msx ) {
		%{ $hFile{hunks}[$pos] } = (
			count        => 0,
			idx          => $pos,
			masked_end   => 0,
			masked_start => 0,
			offset       => 0,
			src_start    => $1,
			tgt_start    => $2,
			useful       => 1
		);

		# We need to chomp the lines:
		for my $line (@lHunk) {
			( defined $line ) or next;
			chomp $line;
			push @{ $hFile{hunks}[$pos]{lines} }, $line;
			$hFile{hunks}[$pos]{count}++;
		} ## end for my $line (@lHunk)
		return 1;
	} ## end if ( $head =~ m/^${mark}\s+-(\d+),\d+\s+[${PLUS}](\d+),\d+\s+${mark}/msx)

	log_error( "Illegal hunk no %d\n(Head: '%s')\nIgnoring...", $hFile{count}, $head );
	$hFile{count}--;

	return 0;
} ## end sub build_hHunk

## @brief Builds output lines for useful hunks and records mask status.
#
#  This subroutine iterates through all hunks in the file, processing only those marked as useful.
#  For each useful hunk, it validates the masked_start value, adds a comment indicating the start mask,
#  generates the hunk header, and appends all lines from the hunk to the output. It also records
#  the masked_end status for every hunk, regardless of usefulness.
#
#  @return Returns 1 on successful completion, or calls hunk_failed and returns undef if validation fails.
sub build_output {

	my $offset = 0; ## Count building up target offsets

	for my $pos ( 0 .. $hFile{count} - 1 ) {
		$hHunk = $hFile{hunks}[$pos]; ## Global shortcut

		# The useless are to be skipped, but we need the hunks masked_end
		if ( $hHunk->{useful} ) {

			# --- Note down the relevant starting mask status ---
			# ---------------------------------------------------
			( defined $hHunk->{masked_start} ) and ( 1 == ( length "$hHunk->{masked_start}" ) )
			        or return hunk_failed(
				'build_output: Hunk '
				        . (
					( defined $hHunk->{masked_start} )
					? "with ${QUOT}" . $hHunk->{masked_start} . $QUOT
					: 'without'
				        )
				        . ' masked_start key found!'
			        );
			$hFile{pwxfile} and ( push @{ $hFile{output} }, '# masked_start ' . $hHunk->{masked_start} );

			# --- Add the header line ---------------------------
			# ---------------------------------------------------
			push @{ $hFile{output} }, get_hunk_head( \$offset );

			# --- Add the hunk lines ----------------------------
			# ---------------------------------------------------
			for my $line ( @{ $hHunk->{lines} } ) {
				( push @{ $hFile{output} }, $line );
			}
		} ## end if ( $hHunk->{useful} )

		# --- Note down the relevant ending mask status -----
		# ---------------------------------------------------
		( defined $hHunk->{masked_end} ) and ( 1 == ( length "$hHunk->{masked_end}" ) )
		        or return hunk_failed(
			'build_output: Hunk '
			        . (
				( defined $hHunk->{masked_end} )
				? "with ${QUOT}" . $hHunk->{masked_end} . $QUOT
				: 'without'
			        )
			        . ' masked_end key found!'
		        );
		$hFile{pwxfile} and push @{ $hFile{output} }, '# masked_end ' . $hHunk->{masked_end};

	} ## end for my $pos ( 0 .. $hFile...)

	return 1;
} ## end sub build_output

## @brief Analyzes a line from a change hunk to identify systemd-related modifications.
#
#  This subroutine processes a line from a diff hunk, extracting relevant information
#  about changes related to systemd components such as elogind, loginctl, systemctl,
#  systemd, and sleep. It identifies the type of change (addition, removal, or neutral),
#  determines if the line is commented, and records the change in the provided data structure.
#
#  @param $pChanges Reference to the changes hash containing analysis results.
#  @param $line_idx Index of the current line being processed.
#  @param $text The text of the line to analyze.
#  @param $is_masked Boolean indicating if the line is masked.
#  @return Returns 1 if the line was successfully analyzed and recorded, 0 otherwise.
sub change_analyze_hunk_line {
	my ( $pChanges, $line_idx, $text, $is_masked ) = @_;
	my $prefix       = $EMPTY;
	my $comment_str  = $EMPTY;
	my $replace_text = $EMPTY;
	my $areas        = q{elogind|loginctl|systemctl|systemd|sleep};

	if ( $text =~ m/^([${PLUS}${SPACE}${DASH}])\s*([${HASH}${SLASH}*]*)\s*(.*(?=${areas}).*)\s*[*${SLASH}${HASH}]*\s*$/misx ) {
		$prefix       = $1;
		$comment_str  = strempty($2);
		$replace_text = $3;
		log_debug( ' => Line % 3d [%s] "%s"', $line_idx + 1, $prefix, $replace_text );
	} else {
		return 0;  # Other lines are of no concern
	}

	# Initialize the change entry if there is  yet
	if ( !( defined $pChanges->{'texts'}{$replace_text} ) ) {
		$pChanges->{'texts'}{$replace_text} = { 'count' => 0, 'changes' => [] };
	}

	# We need a few values...
	my $i      = $pChanges->{$replace_text}{'count'} // 0;                                                         # The count is the next free index
	my $kind   = change_detect_kind($replace_text);
	my $type   = ( ${DASH} eq $prefix ) ? $TYPE_REMOVAL : ( ${PLUS} eq $prefix ) ? $TYPE_ADDITION : $TYPE_NEUTRAL;
	my $alttxt = change_find_alt_text( $kind, $replace_text );
	my $iscomment =
	          ( ( $comment_str =~ m/^[$HASH]+$/msx )     && $hFile{'is_sh'} )  ? $TRUE
	        : ( ( $comment_str =~ m/^[${SLASH}*]+$/msx ) && !$hFile{'is_sh'} ) ? $TRUE
	        :                                                                    $FALSE;

	# Now record our findings
	$pChanges->{$replace_text}{'texts'}{'count'} += 1;
	$pChanges->{$replace_text}{'texts'}{'changes'}[$i] = {
		'alttxt'    => $alttxt,
		'iscomment' => $iscomment,
		'done'      => $FALSE,
		'elogind'   => ( ( $KIND_ELOGIND == $kind ) || ( $KIND_LOGINCTL == $kind ) ) ? 1 : 0,
		'kind'      => $kind,
		'line'      => $line_idx,
		'masked'    => $is_masked,
		'partner'   => undef,
		'prev'      => undef,
		'spliceme'  => 0,
		'systemd'   => ( ( $KIND_SYSTEMD == $kind ) || ( $KIND_SYSTEMCTL == $kind ) ) ? 1 : 0,
		'text'      => $replace_text,
		'type'      => $type
	};

	# Record the change at its line number
	$pChanges->{'lines'}[$line_idx] = $pChanges->{$replace_text}{'texts'}{'changes'}[$i];

	log_debug( " => %-8s type %d at line % 3d: '%s'", ( 0 > $type ) ? 'REMOVAL' : ( 0 < $type ) ? 'ADDITION' : 'Neutral', $kind, $line_idx + 1, $replace_text );

	return 1;
} ## end sub change_analyze_hunk_line

## @brief Checks if a partner change is valid and sets up previous partner tracking.
#
#  This function validates whether the given next partner matches the current change
#  based on text and alternative text. It also ensures the partner has the correct
#  kind and type, and hasn't been processed yet. Additionally, it manages the
#  tracking of previous partners to maintain a chain of relationships.
#
#  @param $change The current change object being evaluated.
#  @param $next_partner The potential partner change to validate.
#  @param $partner_p Reference to the current partner object.
#  @param $prev_partner_p Reference to the previous partner object.
#  @return Returns 1 if the partner is valid and setup is complete, 0 otherwise.
sub change_check_next_partner {
	my ( $change, $next_partner, $partner_p, $prev_partner_p ) = @_;
	my $kind = change_get_partner_kind( $change->{'kind'} );
	my $partner_line =
	        ( defined ${$partner_p} ) ? ${$partner_p}->{'line'} : -1; ## To ensure not to shuffle partner relations
	my $type =
	          ( $TYPE_ADDITION == $change->{'type'} ) ? $TYPE_REMOVAL
	        : ( $TYPE_REMOVAL == $change->{'type'} )  ? $TYPE_ADDITION
	        :                                           $TYPE_NEUTRAL;

	# Check whether at least one text matches the partners alttxt
	# Note: On a systemd-logind <=> elogind change, only one comparison matches, because the alttxt to "elogind" is
	#       "systemd", the "systemd-logind" can not be recreated like that.
	( $next_partner->{'alttxt'} eq $change->{'text'} )
	        or ( $next_partner->{'text'} eq $change->{'alttxt'} )
	        or log_debug('    | => Skipped (Text Mismatch)')
	        and return 0;

	# The potential partner must be of the right kind, have the right type and must not be done, yet
	( $kind == $next_partner->{'kind'} ) and ( $type == $next_partner->{'type'} ) and ( 0 == $next_partner->{'done'} )
	        or log_debug('    | => Skipped (Kind or Type Mismatch)')
	        and return 0;

	# Note: We do not check whether a partner is already set or not, because a set partner might change later.

	# Record this as the prev partner, but store the previous partner as prev, first
	if ( $partner_line > -1 ) {
		log_debug( '    | => Saving line %d as prev', $partner_line + 1 );
		${$partner_p}->{'prev'} = ${$prev_partner_p};  # Save previous partner in current partner
		${$prev_partner_p} = ${$partner_p};            # Set previous partner to current partner
	}

	# We do not take any candidates into account, that are located earlier than an already set partner
	# (Skipping this earlier would disrupt the prev-chain)
	( $next_partner->{'line'} > $partner_line ) or log_debug('    | => Skipped (line too low)') and return 0;

	return 1;
} ## end sub change_check_next_partner

## @brief Handles solo changes in the check process, managing additions, removals, and protected text.
#
#  This subroutine processes individual changes that do not have partners. It skips changes that are already done
#  or have partners defined. Masked changes are marked as done immediately. Protected text additions are also
#  marked as done. For additions, if there's an alternative text and the change involves systemd, it replaces
#  the text with the alternative. For removals, if it's an elogind removal, it reverts the change by adding a space.
#  All processed changes are marked as done.
#
#  @param $pChanges Address of the changees hash
#  @return Returns 1 to indicate successful completion of the processing.
sub change_check_solo_changes {
	my ($pChanges) = @_;

	foreach my $change ( grep { defined } @{ $pChanges->{'lines'} } ) {

		# change is now a reference into $pChange, explicitly at
		#    $pChanges->{string}{'texts'}{'changes'}[no]
		# and has write-back capabilities.

		# If the change is already finished, or if it has a partner defined, nothing is to be done.
		( ( $TRUE == $change->{'done'} ) || ( defined $change->{'partner'} ) ) and next;

		log_change( 'Handle Solo Changes ; Considering Change', $change, 0 );

		# If it is removed from or added to a mask block, we are ok with it
		( $TRUE == $change->{'masked'} ) and change_mark_as_done($change) and next;

		# We have only checked pretexted text additions, yet, not singular removals
		change_is_protected_text( $change->{'text'}, $change->{'iscomment'} ) and change_mark_as_done($change) and next;

		if ( $TYPE_ADDITION == $change->{'type'} ) {

			# Replace the non-protected systemd phrases with our elogind alternative.
			if ( ( ( length $change->{'alttxt'} ) > 0 ) && ( $change->{'systemd'} > 0 ) ) {
				log_debug( "     => Replacing '%s'", $change->{'text'} );
				log_debug( "     => with      '%s'", $change->{'alttxt'} );
				$change->{'text'} = $change->{'alttxt'};
			}
			change_mark_as_done($change);
			next;
		} ## end if ( $TYPE_ADDITION ==...)

		if ( $TYPE_REMOVAL == $change->{'type'} ) {

			# Undo elogind removals, those are probably our own elogind-exclusive functions
			if ( 1 == $change->{'elogind'} ) {
				substr $hHunk->{lines}[ $change->{'line'} ], 0, 1, $SPACE;
				log_debug( "     => Keeping   '%s'", $hHunk->{lines}[ $change->{'line'} ] );
			}
			change_mark_as_done($change);
		} ## end if ( $TYPE_REMOVAL == ...)
	} ## end foreach my $change ( grep {...})

	return 1;
} ## end sub change_check_solo_changes

## @brief Detects the kind of change based on text content.
#
#  This subroutine analyzes the provided text to determine the type of system
#  change being referenced. It uses regular expressions to match keywords
#  associated with different systemd-related services and returns a corresponding
#  constant value.
#
#  @param text The input text to analyze for change detection.
#  @return The detected kind of change as one of the predefined constants,
#          or 0 if no match is found.
sub change_detect_kind {
	my ($text) = @_;
	my $kind =
	          ( $text =~ m/.*elogind.*/msxi )                      ? $KIND_ELOGIND
	        : ( $text =~ m/.*loginctl.*/msxi )                     ? $KIND_LOGINCTL
	        : ( $text =~ m/.*systemd.*/msxi )                      ? $KIND_SYSTEMD
	        : ( $text =~ m/.*systemctl.*/msxi )                    ? $KIND_SYSTEMCTL
	        : ( $text =~ m/.*systemd[-_]sleep[${DOT}]conf.*/msxi ) ? $KIND_SYSTEMD   # The full name is systemd...
	        : ( $text =~ m/.*sleep[${DOT}]conf.*/msxi )            ? $KIND_ELOGIND   # ... and the short name is elogind...
	        :                                                        0;
	return $kind;
} ## end sub change_detect_kind

## @brief Converts source kind references to alternative text for mapping purposes.
#
#  This subroutine transforms text based on the provided source kind, handling
#  specific replacements for elogind, loginctl, systemd, and systemctl references.
#  It supports case-sensitive and case-insensitive replacements, as well as
#  special handling for man page volume numbers and header file naming conventions.
#
#  @param $source_kind The kind of source being processed (e.g., elogind, systemd).
#  @param $source_text The original text to be transformed.
#  @return The transformed text if changes were made; otherwise, an empty string.
sub change_find_alt_text {
	my ( $source_kind, $source_text ) = @_;
	my $alt = $source_text;

	log_debug( 'Searching alt text for source kind %d:', $source_kind );
	log_debug( " txt: '%s'",                             $source_text );

	# 1) 'elogind' => 'systemd'
	if ( $KIND_ELOGIND == $source_kind ) {
		$alt =~ s/elogind/systemd/msgx;
		$source_text eq $alt and $alt =~ s/ELOGIND/SYSTEMD/msgx; ## Try uppercase alternative
		$source_text eq $alt and $alt =~ s/elogind/systemd/misgx; ## Try caseless alternative

		# sleep.conf in elogind is systemd-sleep.conf in systemd
		$alt =~ s/([^${DASH}])(sleep${DOT}conf)/$1systemd-$2/msgx;

		# Note: The replacement of 'systemd-logind' or 'systemd-stable' with elogind can not be reversed this way.
		#       The usr of this subs result (change_map_hunk_lines()) has to do this itself when searching for a match.
	} ## end if ( $KIND_ELOGIND == ...)

	# 2) 'loginctl' => 'systemctl'
	if ( $KIND_LOGINCTL == $source_kind ) {
		$alt =~ s/loginctl/systemctl/msgx;
		$source_text eq $alt and $alt =~ s/LOGINCTL/SYSTEMCTL/msgx; ## Try uppercase alternative
		$source_text eq $alt and $alt =~ s/loginctl/systemctl/misgx; ## Try caseless alternative
	}

	# 3) 'systemd' => 'elogind'
	if ( $KIND_SYSTEMD == $source_kind ) {
		$alt =~ s/systemd[-_]logind/elogind/msgx;
		$source_text eq $alt and $alt =~ s/systemd[-_]stable/elogind/msgx; ## Try the stable alternative
		$source_text eq $alt and $alt =~ s/systemd/elogind/msgx; ## Try plain alternative
		$source_text eq $alt and $alt =~ s/SYSTEMD/ELOGIND/msgx; ## Try uppercase alternative
		$source_text eq $alt and $alt =~ s/systemd/elogind/misgx; ## Try caseless alternative

		# If we are in a man page, systemd is placed in volume 1, while elogind is placed in volume 8
		$source_text ne $alt and $alt =~ s/<manvolnum>1<\/manvolnum>/<manvolnum>8<\/manvolnum>/msgx;

		# systemd-sleep.conf is *not* elogind-sleep.conf, but just sleep.conf in elogind
		$alt =~ s/(?:systemd|elogind)${DASH}(sleep${DOT}conf)/$1/msgx;
	} ## end if ( $KIND_SYSTEMD == ...)

	# 4) 'systemctl' => 'loginctl'
	if ( $KIND_SYSTEMCTL == $source_kind ) {
		$alt =~ s/systemctl/loginctl/msgx;
		$source_text eq $alt and $alt =~ s/SYSTEMCTL/LOGINCTL/msgx; ## Try uppercase alternative
		$source_text eq $alt and $alt =~ s/systemctl/loginctl/misgx; ## Try caseless alternative
	}

	# In some meson files, we need the variable "systemd_headers".
	# This refers to the systemd API headers that get installed,
	# and must therefore not be renamed to elogind_headers.
	$alt =~ s/elogind_headers/systemd_headers/msg;

	my $alttxt = ( $alt eq $source_text ) ? $EMPTY : $alt;
	log_debug( " alt: '%s'", ( ( length $alttxt ) > 0 ) ? $alttxt : 'n/a' );

	return $alttxt;
} ## end sub change_find_alt_text

## @brief Scan the change hash for a partner to the given change
#
# For a removal, an'addition is searched and vice versa.
# for systemd/systemctl, elogind/loginct is searched and vice versa
#
# @param[in,out] $pChanges  The pointer to the full %hChanges hash
# @param[in,out] $change    The pointer to the explicit change to handle
# @return Always 1, we never fail.
sub change_find_and_set_partner {
	my ( $pChanges, $change ) = @_;
	my $lines_ref    = $pChanges->{'lines'};
	my $max_idx      = $change->{'line'};
	my $partner      = $change->{'partner'}; ## The last partner found
	my $prev_partner = undef; ## The previous partner found

	log_debug( ' => Searching Partner for line %d', $max_idx + 1 );
	( defined $partner ) and log_debug( '    Current partner at line %d', $partner->{'line'} + 1 );

	for my $i ( 0 .. $#{$lines_ref} ) {
		( defined $lines_ref->[$i] ) or next;  # skip gaps that come from using only relevant line numbers as indices
		( $i >= $max_idx ) and last;           # stop at the change we map
		my $next_partner = $lines_ref->[$i];

		log_debug( '    | Check line %d', $i + 1 );

		# Do the relevant checks in another sub
		change_check_next_partner( $change, $next_partner, \$partner, \$prev_partner ) or next;

		# If all conditions are met, record this as the next viable candidate
		log_debug( '    | => Storing line %d as partner', $next_partner->{'line'} + 1 );
		$partner = $next_partner;              # Set current partner to next partner found
	} ## end for my $i ( 0 .. $#{$lines_ref...})

	# At this point we have zero, one or two+ partners. The first two are easy.
	( defined $partner ) or return 1; ## Nothing to do

	log_debug( '    | Found Partner at line %d', $partner->{'line'} + 1 );

	# If we have found 2+ partners, 'prev' is now set
	if ( defined $prev_partner ) {
		$partner->{'prev'} = $prev_partner;    # Store prev_partner to save the backward chain

		# If we have two partners, we must guess which one is correct. The situation might be:
		#   first partner
		#   ...
		#   second partner
		#   ...
		#   this change
		#   ... no further occurrence of this change
		# In this case it is valid to assume that the first is a solitary removal/addition and the second
		# partner teams up with this change. This assumption might be wrong, but it would not change the outcome.
		# However, if we have the following situation, the correct partnering is crucial:
		#   first partner
		#   ...
		#   second partner
		#   ...
		#   this change
		#   ... not seen yet ...
		#   similar change to this one, not discovered, yet.
		# In this case the first partner must be teamed with this change, and the second will later be teamed with the next
		# similar change. Unfortunately we do not know yet that it'll come.
		# But that is why we do not rule out entries with an already set partner above, we can use that information now:
		if ( ( defined $partner->{'partner'} ) && ( $change != $partner->{'partner'} ) ) {
			log_debug( '    | => Moving Partners partner at line %d up', $partner->{'partner'}{'line'} + 1 );
			change_move_partner_up($partner) or croak('found to many partners, this should be impossible!');
		}
	} ## end if ( defined $prev_partner)

	# The rest is easy, just set the partner to the last found
	log_debug( ' <= Setting Partners %d <=> %d', $change->{'line'} + 1, $partner->{'line'} + 1 );
	$change->{'partner'}  = $partner;
	$partner->{'partner'} = $change;

	return 1;
} ## end sub change_find_and_set_partner

## @brief Returns the partner kind for a given kind.
#
#  This function maps one kind to its corresponding partner kind. It is used to
#  switch between systemd and elogind related constants.
#
#  @return The partner kind corresponding to the input kind.
sub change_get_partner_kind {
	my ($kind) = @_;

	( $KIND_SYSTEMD == $kind )   and return $KIND_ELOGIND;
	( $KIND_SYSTEMCTL == $kind ) and return $KIND_LOGINCTL;
	( $KIND_ELOGIND == $kind )   and return $KIND_SYSTEMD;
	( $KIND_LOGINCTL == $kind )  and return $KIND_SYSTEMCTL;

	croak("change_get_partner_kind() called with invalid kind '$kind'!");
} ## end sub change_get_partner_kind

## @brief Handles addition changes in a set of file modifications.
#
#  This subroutine processes additions to check whether they follow a removal. It ensures that
#  additions are correctly handled based on their relationship with partner removals. Specifically,
#  it handles direct renames between elogind and systemd, checks for movement into/out of comments
#  or masks, and applies appropriate text changes.
#
#  @return Returns 1 upon successful completion.
sub change_handle_additions {
	my ($pChanges) = @_;

	log_debug('Checking Additions ...');

	# Go through additions and check whether they follow a removal
	my $lines_ref = $pChanges->{'lines'};
	for my $i ( 0 .. $#{$lines_ref} ) {
		( defined $lines_ref->[$i] ) or next;  # skip gaps that come from using only relevant line numbers as indices
		my $change = $lines_ref->[$i];         # change is now at $hChanges{string}{'texts'}{'changes'}[no] with write-back capabilities

		log_change( 'Handle Additions ; Considering Change', $change,              0 );
		log_change( '--- ==> Partner : ---',                 $change->{'partner'}, 1 );

		# Skip changes that are done and only keep additions
		( ( $TRUE == $change->{'done'} ) || ( $TYPE_ADDITION != $change->{'type'} ) ) and next;

		# At this point only entries with a partner can be not done
		my $partner = $change->{'partner'};
		( defined $partner ) or log_error( "Fatal: Line %d '%s' has no partner!", $change->{'line'}, $change->{'text'} ) and croak('Cannot continue!');

		# We only handle forward additions, so the line number of the addition must be greater than that of the removal
		( $change->{'line'} > $partner->{'line'} ) or next; ## change_handle_removals() takes care of forward removals.

		# If they are direct renames, undo them if they go from elogind to systemd, but accept if it is the other way round
		if ( $change->{'line'} == ( $partner->{'line'} + 1 ) ) {
			( $TRUE == $change->{'systemd'} ) and change_undo( $partner, $change, $i );

			# No change for the other way around, just mark as done
			change_mark_as_done($change); ## Also marks the partner
			next;
		} ## end if ( $change->{'line'}...)

		# If they are further away, check comment and mask status. We do not allow a diff to move lines into and out of masks
		# However, if the move is into a comment is is okay, but not out of a comment. We had reason for commenting something out.
		if (       ( $partner->{'masked'} != $change->{'masked'} )
			|| ( ( $TRUE == $partner->{'iscomment'} ) && ( $FALSE == $change->{'iscomment'} ) ) )
		{
			## The change moves commented line out of the comment, or changes a masked status
			change_undo( $partner, $change, $i );
			change_mark_as_done($change);
			next;
		} ## end if ( ( $partner->{'masked'...}))

		# In all other cases we allow the move, but reverse the text change if it is elogind->systemd and not a protected text
		change_is_protected_text( $change->{'text'}, $change->{'iscomment'} ) or ( $TRUE == $change->{'systemd'} ) and change_use_alt($change);
		change_mark_as_done($change);
	} ## end for my $i ( 0 .. $#{$lines_ref...})

	return 1;
} ## end sub change_handle_additions

## @brief Handles false positives in changes by marking certain modifications as done.
#
#  This subroutine filters through a list of changes and identifies modifications that
#  should not be processed further based on specific patterns. It checks for references
#  to systemd GitHub or .io sites, protected text phrases, and gettext domain usage,
#  marking them as done to prevent unnecessary processing.
#
#  @return Returns 1 to indicate successful completion of the function.
sub change_handle_false_positives {
	my ($pChanges) = @_;

	foreach my $change ( grep { defined } @{ $pChanges->{'lines'} } ) {

		# change is now a reference into $pChange, explicitly at
		#    $pChanges->{string}{'texts'}{'changes'}[no]
		# and has write-back capabilities.
		( $FALSE == $change->{'done'} ) and ( $TYPE_ADDITION == $change->{'type'} ) or next; ## Already handled or not an addition
		my $text = $change->{'text'};

		log_change( 'Checking Change Against Reserved Expressions', $change,              0 );
		log_change( '--- ==> Partner : ---',                        $change->{'partner'}, 1 );

		# 1) References to the systemd github or .io site must not be changed.
		if ( ( $text =~ m/github[${DOT}]com[${SLASH}]systemd/msx ) || ( $text =~ m/systemd[${DOT}]io/msx ) ) {

			# If it is the issue tracker, look at the issue number. elogind is in the 3-digit area, systemd is in the 5-digit area
			if ( $text =~ m/github[${DOT}]com[${SLASH}]systemd[${SLASH}]systemd[${SLASH}]issues[${SLASH}](\d+)/msx ) {
				my $num = $1;
				( ( length "$num" ) > 4 ) and change_mark_as_done($change) and next;  # clearly a systemd issue
			}

			# If a removal exists that was a link to the elogind github main page, then allow the switch back. We had our reasons!
			my $partner      = $change->{'partner'};
			my $partner_text = ( defined $partner ) ? $partner->{'text'} // $EMPTY : $EMPTY;
			if ( $partner_text =~ m/github[${DOT}]com[${SLASH}]elogind[${SLASH}]elogind/msx ) {
				next;
			}

			change_mark_as_done($change) and next;
		} ## end if ( ( $text =~ m/github[${DOT}]com[${SLASH}]systemd/msx...))

		# 2) Several words/paths/phrases are protected
		change_is_protected_text( $text, $change->{'iscomment'} ) and change_mark_as_done($change) and next;

		# Also the gettext domain is always "systemd", and varlink works via io.systemd domain.
		( ( $text =~ m/gettext-domain="systemd/msx ) || ( $text =~ m/io[.]systemd/msx ) ) and change_mark_as_done($change) and next;
	} ## end foreach my $change ( grep {...})

	return 1;
} ## end sub change_handle_false_positives

## @brief Handles removal changes in a set of code modifications.
#
#  This subroutine processes removal changes to determine whether they follow an addition,
#  and applies appropriate actions based on the relationship between the removal and its partner.
#  It handles cases such as direct renames, masked/commented line movements, and protection logic.
#
#  @return Returns 1 upon successful completion.
sub change_handle_removals {
	my ($pChanges) = @_;

	log_debug('Checking Removals ...');

	# Go through removals and check whether they follow an addition
	my $lines_ref = $pChanges->{'lines'};
	for my $i ( 0 .. $#{$lines_ref} ) {
		( defined $lines_ref->[$i] ) or next;  # skip gaps that come from using only relevant line numbers as indices
		my $change = $lines_ref->[$i];         # change is now at $hChanges{string}{'texts'}{'changes'}[no] with write-back capabilities

		log_change( 'Handle Removals ; Considering Change', $change,              0 );
		log_change( '--- ==> Partner : ---',                $change->{'partner'}, 1 );

		# Skip changes that are done and only keep removals
		( ( $TRUE == $change->{'done'} ) || ( $TYPE_REMOVAL != $change->{'type'} ) ) and next;

		# At this point only entries with a partner can be not done
		my $partner = $change->{'partner'};
		( defined $partner ) or log_error( "Fatal: Line %d '%s' has no partner!", $change->{'line'} + 1, $change->{'text'} ) and croak('Cannot continue!');

		# We only handle forward removals, so the line number of the removal must be greater than that of the addition
		( $change->{'line'} > $partner->{'line'} ) or next; ## change_handle_additions() takes care of forward additions.

		# If they are direct renames, undo them if they go from elogind to systemd, but accept if it is the other way round
		if ( $change->{'line'} == ( $partner->{'line'} + 1 ) ) {
			( $TRUE == $change->{'elogind'} ) and change_undo( $change, $partner, $i );

			# No change for the other way around, just mark as done
			change_mark_as_done($change); ## Also marks the partner
			next;
		} ## end if ( $change->{'line'}...)

		# If they are further away, check comment and mask status
		if (       ( ( $FALSE == $partner->{'masked'} ) && ( $TRUE == $change->{'masked'} ) )
			|| ( ( $FALSE == $partner->{'iscomment'} ) && ( $TRUE == $change->{'iscomment'} ) ) )
		{
			## The change moves a masked or commented line out of the mask/comment
			( $TRUE == $change->{'elogind'} )                    #
			        and change_reverse( $change, $partner, $i )  # Apply the elogind->systemd change to the change, splice the addition
			        or change_undo( $change, $partner, $i );     # Remove the systemd->elogind move, although this seems to be impossibly to ever happen.
			change_mark_as_done($change);                        # Also marks the partner
			next;
		} ## end if ( ( ( $FALSE == $partner...)))

		# In all other cases we allow the move, but reverse the text change if it is elogind->systemd and the partner is not protected
		change_is_protected_text( $partner->{'text'}, $partner->{'iscomment'} ) or ( $TRUE == $change->{'elogind'} ) and change_use_alt($partner);
		change_mark_as_done($change); ## Also marks the partner
	} ## end for my $i ( 0 .. $#{$lines_ref...})

	return 1;
} ## end sub change_handle_removals

## @brief Checks if text contains protected patterns that should not be replaced.
#
#  This function evaluates whether a given text contains patterns that are
#  protected from replacement. These patterns include specific paths like
#  /run/systemd, systemd website URLs, org.freedesktop.systemd strings,
#  references to systemd[1], specific systemd services, and various systemd
#  daemons, keywords, and products. The function logs debug information for
#  each matched protected pattern.
#
#  @param $text The text to check for protected patterns.
#  @param $is_commented Indicates if the text is within a comment block.
#  @return Returns 1 if any protected pattern is found, otherwise returns 0.
sub change_is_protected_text {
	my ( $text, $is_commented ) = @_;

	log_debug( "Checking whether '%s' is protected", $text );

	# 1) /run/systemd/ must not be changed, as other applications
	#    rely on that naming.
	# Note: The /run/elogind.pid file is not touched by that, as
	#       systemd does not have something like that.
	$text =~ m/\/run\/systemd/msx and log_debug( "     => Protected '%s'", 'run/systemd' ) and return 1;

	# 2) Several systemd website urls must not be changed, too
	for my $pat ( keys %SYSTEMD_URLS ) {
		$text =~ m/$pat/msx and log_debug( "     => Protected '%s'", 'systemd URL' ) and return 1;
	}

	# 3) To be a dropin-replacement, we also need to not change any org[./]freedesktop[./]systemd strings
	$text =~ m/\/?org[.\/]freedesktop[.\/]systemd/msx and log_debug( "     => Protected '%s'", 'freedesktop/systemd' ) and return 1;

	# 4) Do not replace referrals to systemd[1]
	$text =~ m/systemd\[1\]/msx and log_debug( "     => Protected '%s'", 'man systemd' ) and return 1;

	# 5) Specific systemd services that might be mentioned in comments that are not masked:
	my $systemd_services = q{user-sessions|logind};
	            ( $is_commented > 0 )
	        and ( ( $text =~ m/systemd[-_]($systemd_services)[${DOT}]service/msx ) )
	        and log_debug( "     => Protected '%s'", 'systemd service' )
	        and return 1;

	# 6) References to systemd-homed and other tools not shipped by elogind
	#    must not be changed either, or users might think elogind has its
	#    own replacements.
	is_systemd_only($text) and log_debug('     => protected systemd-only') and return 1;

	return 0;
} ## end sub change_is_protected_text

## @brief Maps additions and removals in changes to find corresponding partner lines for systemd<->elogind naming changes.
#
#  This subroutine processes a list of changes to identify matching additions and removals that represent
#  moves rather than pure modifications. It specifically handles systemd additions and elogind removals,
#  mapping them to their counterparts to distinguish real code changes from naming convention adjustments.
#
#  @return Returns 1 upon successful completion of the mapping process.
sub change_map_hunk_lines {
	my ($pChanges) = @_;

	# 1) Loop over additions to find previous matching removals
	# -----------------------------------------------------------------------------------------------------------------
	foreach my $change ( grep { defined } @{ $pChanges->{'lines'} } ) {

		# change is now a reference into $pChange, explicitly at
		#    $pChanges->{string}{'texts'}{'changes'}[no]
		# and has write-back capabilities.
		log_change( 'Scanning Additions ; Considering Change', $change, 0 );
		( $FALSE == $change->{'done'} ) and ( $TYPE_ADDITION == $change->{'type'} ) or next; ## Already handled or not an addition
		( 1 == $change->{'systemd'} ) or next; ## only systemd additions are relevant
		change_find_and_set_partner( $pChanges, $change );
		log_change( 'Scanning Additions ; Change Mapped', $change,              0 );
		log_change( '--- ==> Partner : ---',              $change->{'partner'}, 1 );
	} ## end foreach my $change ( grep {...})

	# We now have mapped regular diffs that remove something on line n and add it back, changed on line n+x.

	# 2) Loop over removals to find previous matching additions
	# -----------------------------------------------------------------------------------------------------------------
	foreach my $change ( grep { defined } @{ $pChanges->{'lines'} } ) {
		log_change( 'Scanning Removals ; Considering Change', $change, 0 );
		( $FALSE == $change->{'done'} ) and ( $TYPE_REMOVAL == $change->{'type'} ) or next; ## Already handled or not a removal
		( 1 == $change->{'elogind'} ) or next; ## only elogind removals are relevant
		change_find_and_set_partner( $pChanges, $change );
		log_change( 'Scanning Removals ; Change Mapped', $change,              0 );
		log_change( '--- ==> Partner : ---',             $change->{'partner'}, 1 );
	} ## end foreach my $change ( grep {...})

	# The second run mapped real moves, so the line was not only changed, it was also moved
	# At this point we can assume, that unpartnered removals and additions are real changes to the source code and no longer
	# change systemd<->elogind naming only.

	return 1;
} ## end sub change_map_hunk_lines

## @brief Marks a change and its partner as done.
#
#  This subroutine sets the 'done' attribute of the change and its partner to true,
#  indicating that the change has been processed. It also logs the action for
#  debugging purposes.
#
#  @return Returns 1 to indicate successful completion.
sub change_mark_as_done {
	my ($change) = @_;
	my $partner = $change->{'partner'};
	log_change( 'Marking Change and partner as done', $change,              0 );
	log_change( '--- ==> Partner : ---',              $change->{'partner'}, 1 );
	$change->{'done'} = $TRUE;
	if ( defined $partner ) {
		$partner->{'done'} = $TRUE;
	}
	return 1;
} ## end sub change_mark_as_done

## @brief Recursively moves a partner up the changes previous chain.
#
#  This function traverses the previous chain of a change to move its partner
#  up towards the earliest point in the chain. If the end of the chain is
#  reached, the partner is removed from the chain and becomes a solo.
#  If an earlier change already has a partner, it is moved up first to make
#  space for the current partner.
#
#  @return Returns $TRUE on success, $FALSE on failure.
sub change_move_partner_up {
	my ($change) = @_;
	( defined $change )              or confess('Serious bug, change is undef!');
	( defined $change->{'partner'} ) or confess('Serious bug, partner is undef!');

	# Simple recursive function to move partners up a changes prev chain.
	my $partner = $change->{'partner'};
	my $prev    = $change->{'prev'};
	if ( !( defined $prev ) ) {

		# end of chain found, earliest partner will become a solo
		if ( defined $partner ) {
			$partner->{'partner'} = undef;
			$change->{'partner'}  = undef;
		}
		return $TRUE;
	} ## end if ( !( defined $prev ...))

	# If prev has already a partner, move it up first to make space for ours
	my $r = ( defined $prev->{'partner'} ) ? change_move_partner_up($prev) : $TRUE;
	( $TRUE == $r ) or return $FALSE; ## Followup from running out of prevs above

	# Now we can move the partner to prev
	$prev->{'partner'}    = $partner;
	$partner->{'partner'} = $prev;
	$change->{'partner'}  = undef;

	return $TRUE;
} ## end sub change_move_partner_up

## @brief Protects lines from removal changes in a hunk.
#
#  This subroutine iterates through the provided changes and identifies those of type
#  TYPE_REMOVAL. For each such change, it marks the corresponding line in the hunk
#  as protected by adding it to the %hProtected hash. This prevents the line from
#  being removed during subsequent processing.
#
#  @return Returns 1 to indicate successful completion.
sub change_protect_removals {
	my ($pChanges) = @_;

	# Loop over lines and note down those to be protected
	# -----------------------------------------------------------------------------------------------------------------
	foreach my $change ( grep { defined } @{ $pChanges->{'lines'} } ) {
		( $TYPE_REMOVAL == $change->{'type'} ) or next;
		my $line = $hHunk->{lines}[ $change->{'line'} ];
		$hProtected{$line} = 1;
		log_debug( "Protecting line % 3d: '%s'", $change->{'line'} + 1, $line );
	} ## end foreach my $change ( grep {...})

	return 1;
} ## end sub change_protect_removals

sub change_remove {
	my ( $to_splice, $at_line ) = @_;

	$to_splice->{'spliceme'} = $at_line;
	log_debug( "     => Splicing % 3d: '%s'", $at_line + 1, $hHunk->{lines}[ $to_splice->{'spliceme'} ] );

	return 1;
} ## end sub change_remove

## @brief Changes a line by reversing its first character and marks it for splicing.
#
#  This subroutine modifies a line in the hunk by changing its first character
#  and then marks the line for splicing. It logs debug information before and
#  after the change.
#
#  @param $to_change Hash reference to the line to be changed.
#  @param $to_splice Hash reference to the line to be spliced.
#  @param $at_line Line number where the splice operation will occur.
#  @return Returns 1 to indicate successful completion.
sub change_reverse {
	my ( $to_change, $to_splice, $at_line ) = @_;

	log_debug( "     => Changing  '%s'", $hHunk->{lines}[ $to_change->{'line'} ] );
	change_use_alt($to_change);
	substr $hHunk->{lines}[ $to_change->{'line'} ], 0, 1, $SPACE;
	log_debug( "           => To  '%s'", $hHunk->{lines}[ $to_change->{'line'} ] );
	change_remove( $to_splice, $at_line );

	return 1;
} ## end sub change_reverse

## @brief Removes specified lines from a hunk based on splice markers.
#
#  This subroutine processes a list of changes and identifies lines marked for splicing.
#  It then removes those lines from the hunk in reverse order to maintain correct indexing.
#  The count of lines in the hunk is adjusted accordingly.
#
#  @return Returns 1 to indicate successful completion.
sub change_splice_the_undone {
	my ($pChanges) = @_;

	# 1) Loop over lines and note down those to be spliced
	# -----------------------------------------------------------------------------------------------------------------
	my %hSplices = ();
	foreach my $change ( grep { defined } @{ $pChanges->{'lines'} } ) {
		( $change->{'spliceme'} > 0 ) or next;
		$hSplices{ $change->{'spliceme'} } = 1;
		log_debug( "Splice line % 3d: '%s'", $change->{'spliceme'} + 1, $change->{'text'} );
	}

	# 2) Loop over the splices and remove them, use reverse order to not get confused
	# -----------------------------------------------------------------------------------------------------------------
	for my $l ( reverse sort { $a <=> $b } keys %hSplices ) {
		splice @{ $hHunk->{lines} }, $l, 1;
		--$hHunk->{count};
	}

	return 1;
} ## end sub change_splice_the_undone

## @brief Undoes a change by marking a line to keep and preparing another for splicing.
#
#  This function modifies the hunk's lines array to indicate that a line should be kept
#  (by changing its first character to a space) and prepares another line for splicing
#  by setting the spliceme attribute. It also logs debug information about both actions.
#
#  @param $to_keep Hash reference containing the line number to keep.
#  @param $to_splice Hash reference containing information about the line to splice.
#  @param $at_line Line number where the splicing should occur.
#  @return Returns 1 to indicate successful completion.
sub change_undo {
	my ( $to_keep, $to_splice, $at_line ) = @_;

	substr $hHunk->{lines}[ $to_keep->{'line'} ], 0, 1, $SPACE;
	log_debug( "     => Keeping  % 3d: '%s'", $to_keep->{'line'} + 1, $hHunk->{lines}[ $to_keep->{'line'} ] );
	change_remove( $to_splice, $at_line );

	return 1;
} ## end sub change_undo

## @brief Replaces text in a hunk line with its alternative text.
#
#  This subroutine modifies a specific line in the hunk by replacing the old text
#  with the new alternative text. It logs the change before and after the replacement
#  for debugging purposes.
#
#  @return Returns 1 to indicate successful completion of the text replacement.
sub change_use_alt {
	my ($change) = @_;
	my $lno      = $change->{'line'};
	my $newText  = $change->{'alttxt'};
	my $oldText  = $change->{'text'};

	log_debug( "     => Change  % 3d: '%s'", $lno + 1, $hHunk->{lines}[$lno] );
	$hHunk->{lines}[$lno] =~ s{\Q$oldText\E}{$newText}ms;
	log_debug( "     =>   To    % 3d: '%s'", $lno + 1, $hHunk->{lines}[$lno] );

	return 1;
} ## end sub change_use_alt

## @brief Checks for and corrects misplaced blank additions and unpleasant removals in hunks.
#
# This subroutine examines each line in a hunk to identify and correct specific
# patterns of blank lines that may be misplaced or cause issues. It handles two main cases:
# 1. A blank addition line immediately following a mask or insert start line, which it swaps
#    with the previous line to maintain proper context.
# 2. A blank removal line immediately preceding a mask or insert end line, and followed by
#    a non-blank line, which it converts to a space to avoid disrupting the diff structure.
#
# @return Non-zero on successful processing, zero if the hunk is not defined or not useful.
sub check_blanks {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Checking useful blank additions ...');

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Check for misplaced addition
		if (       ( ${$line} =~ m/^[${PLUS}]\s*$/msx )
			&& ( $i > 0 )
			&& ( ( is_mask_start( $hHunk->{lines}[ $i - 1 ] ) || is_insert_start( $hHunk->{lines}[ $i - 1 ] ) ) ) )
		{
			# Simply swap the lines
			my $tmp = ${$line};
			${$line} = $hHunk->{lines}[ $i - 1 ];
			$hHunk->{lines}[ $i - 1 ] = $tmp;
			next;
		} ## end if ( ( ${$line} =~ m/^[${PLUS}]\s*$/msx...))

		# Check for unpleasant removals
		if (       ( ${$line} =~ m/^[${DASH}]\s*$/msx )
			&& ( $i > 0 )
			&& ( ( is_mask_end( $hHunk->{lines}[ $i - 1 ] ) || is_insert_end( $hHunk->{lines}[ $i - 1 ] ) ) )
			&& ( $i < ( $hHunk->{count} - 1 ) )
			&& ( !( $hHunk->{lines}[ $i + 1 ] =~ m/^[${DASH}${PLUS}${SPACE}]\s*$/msx ) ) )
		{
			# Revert the removal
			substr ${$line}, 0, 1, $SPACE;
			next;
		} ## end if ( ( ${$line} =~ m/^[${DASH}]\s*$/msx...))

	} ## end for my $i ( 0 .. $hHunk...)

	return hunk_is_useful();
} ## end sub check_blanks

## @brief Checks for proper comment block formatting in a hunk.
#
# This subroutine verifies that comment blocks, specifically those starting
# with /* or // and containing "elogind", are properly formatted. It ensures
# that multiline comments are correctly started and ended, and that lines
# within comment blocks are properly indented. If a line is part of a comment
# block but not protected, it will be unindented to indicate it's not part
# of the actual code.
#
# @param hHunk A reference to a hash containing information about the hunk,
#              including lines and count.
# @return 1 if the comments are correctly formatted, 0 otherwise.
sub check_comments {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Checking comments...');

	my $in_comment_block = 0;

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Check for comment block start
		# -----------------------------
		if ( ${$line} =~ m/^[${DASH}]\s*(\/[${STAR}]+|\/\/+)\s+.*elogind/msx ) {

			# Sanity check:
			$in_comment_block
			        and return hunk_failed('check_comments: Comment block start found in comment block!');

			# Only start the comment block if this is really a multiline comment
			( ( ${$line} =~ m/^[${DASH}]\s*\/[${STAR}]+/msx ) && !( ${$line} =~ m/[${STAR}]\/[^\/]*$/msx ) )
			        and $in_comment_block = 1;

			# Revert the substract *if* this is not in a mask block, but only if the name reversal checker has not marked this as protected
			$in_mask_block and ( 1 > $in_else_block ) or ( defined $hProtected{ ${$line} } ) or substr ${$line}, 0, 1, $SPACE;

			next;
		} ## end if ( ${$line} =~ m/^[${DASH}]\s*(\/[${STAR}]+|\/\/+)\s+.*elogind/msx)

		# Check for comment block end
		# -----------------------------
		if ( $in_comment_block && ( ${$line} =~ m/^[${DASH}].*[${STAR}]\/\s*$/msx ) ) {
			( defined $hProtected{ ${$line} } ) or substr ${$line}, 0, 1, $SPACE;
			$in_comment_block = 0;
			next;
		}

		# Check for comment block line
		# -----------------------------
		if ( $in_comment_block && ( ${$line} =~ m/^[${DASH}]/msx ) ) {

			# Note: We do not check for anything else, as empty lines must be allowed.
			( defined $hProtected{ ${$line} } ) or substr ${$line}, 0, 1, $SPACE;
			next;
		} ## end if ( $in_comment_block...)

		# If none of the above applied, the comment block is over.
		$in_comment_block = 0;
	} ## end for my $i ( 0 .. $hHunk...)

	return hunk_is_useful();
} ## end sub check_comments

## @brief Check and process debug constructs in a hunk
#
# This subroutine verifies the correct usage of debug constructs within a code hunk,
# particularly focusing on ENABLE_DEBUG_ELOGIND preprocessor directives. It ensures that
# #if, #else, and #endif blocks are properly nested and that debug-specific lines
# (marked with '-') are correctly processed. The function also handles special cases
# like log_debug_elogind() calls and nested elogind mask/insert blocks.
#
# @return Returns 1 on successful processing, 0 otherwise.
sub check_debug {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Checking debug constructs ...');

	# Count non-elogind block #ifs. This is needed, so normal
	# #if/#else/#/endif constructs can be put inside both the
	# debug and the release block.
	my $regular_ifs   = 0;
	my $is_debug_func = 0; ## Special for log_debug_elogind()

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# entering a debug construct block
		# ---------------------------------------
		if ( ${$line} =~ m/^-[${HASH}]if.+ENABLE_DEBUG_ELOGIND/msx ) {
			## Note: Here it is perfectly fine to be in an elogind mask or insert block.
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'
			$in_insert_block++; ## Increase instead of setting this to 1.
			next;
		} ## end if ( ${$line} =~ m/^-[${HASH}]if.+ENABLE_DEBUG_ELOGIND/msx)

		# Count regular #if
		${$line} =~ m/^-[${HASH}]if/msx and ++$regular_ifs;

		# Switching to the release variant.
		# ---------------------------------------
		if ( ( ${$line} =~ m/^-[${HASH}]else/msx ) && $in_insert_block && !$regular_ifs ) {
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'
			$in_else_block++; ## Increase instead of setting this to 1.
			next;
		}

		# ending a debug construct block
		# ---------------------------------------
		if ( ${$line} =~ m/^[${DASH}][${HASH}]endif\s*\/\/\/?.*ENABLE_DEBUG_/msx ) {
			( !$in_insert_block )
			        and return hunk_failed('check_debug: #endif // ENABLE_DEBUG_* found outside any debug construct');
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'
			$in_insert_block--; ## Decrease instead of setting to 0. This allows such
			$in_else_block--; ## blocks to reside in regular elogind mask/insert blocks.
			next;
		} ## end if ( ${$line} =~ m/^[${DASH}][${HASH}]endif\s*\/\/\/?.*ENABLE_DEBUG_/msx)

		# end regular #if
		# ---------------------------------------
		${$line} =~ m/^[${DASH}][${HASH}]endif/msx and --$regular_ifs;

		# Check for log_debug_elogind()
		# ---------------------------------------
		if ( ${$line} =~ m/^[${DASH}].*log_debug_elogind\s*[(]/msx ) {
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'
			${$line} =~ m/[)]\s*;/smx or ++$is_debug_func;
			next;
		}

		# Remove '-' prefixes in all lines within the debug construct block
		# -------------------------------------------------------------------
		if ( ( ${$line} =~ m/^[${DASH}]/msx ) && ( $in_insert_block || $is_debug_func ) ) {
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'

			# Note: Everything in *any* insert block must not be removed anyway.
		}

		# Check for the end of a multiline log_debug_elogind() call
		# ---------------------------------------------------------
		$is_debug_func and ${$line} =~ m/[)]\s*;/msx and --$is_debug_func;

	} ## end for my $i ( 0 .. $hHunk...)

	return hunk_is_useful();
} ## end sub check_debug

## @brief Checks and modifies patch lines that remove elogind_ function calls to prevent accidental deletion
#
#  This subroutine processes patch hunks to identify lines that remove calls to functions
#  prefixed with 'elogind_'. It prevents accidental removal of these function calls,
#  particularly handling multi-line function calls correctly by tracking continuation lines
#  and using a protection hash to avoid modifying protected lines.
#
# @return None. Modifies input hunk lines in-place.
sub check_func_removes {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	# Not used in pwx files (meson, xml, sym)
	$hFile{pwxfile} and return 1;

	log_debug('Checking function removals ...');

	# Needed for multi-line calls
	my $is_func_call = 0;

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Check for elogind_*() call
		# -------------------------------------------------------------------
		if ( ${$line} =~ m/^[${DASH}].*elogind[_]\S+\s*[(]/msx ) {
			( defined $hProtected{ ${$line} } ) or substr ${$line}, 0, 1, $SPACE; ## Remove '-'
			${$line} =~ m/[)]\s*;/msx or ++$is_func_call;
			next;
		}

		# Remove '-' prefixes in all lines that belong to an elogind_*() call
		# -------------------------------------------------------------------
		if ( ( ${$line} =~ m/^[${DASH}]/msx ) && $is_func_call && !( defined $hProtected{ ${$line} } ) ) {
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'
		}

		# Check for the end of a multiline elogind_*() call
		# -------------------------------------------------------------------
		$is_func_call and ${$line} =~ m/[)]\s*;/msx and --$is_func_call;
	} ## end for my $i ( 0 .. $hHunk...)

	return hunk_is_useful();
} ## end sub check_func_removes

## @brief Checks for and removes empty mask blocks, converting relevant else clauses.
#
#  This function processes a hunk of code to identify and remove empty elogind mask blocks.
#  It also handles conversion of certain else clauses that immediately follow mask starts,
#  and ensures proper handling of #endif lines when needed. The function operates on
#  the global hHunk hash reference and modifies its contents in-place, without affecting
#  global values.
#
#  The function tracks the state of mask and insert blocks using local variables to avoid
#  interference with other processing. It ensures that only appropriate conversions are made,
#  considering spacing constraints within the patch.
#
# @return Returns 1 upon completion.
sub check_empty_masks {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Checking empty mask removals ...');

	# We must not touch the global values!
	# Note: We search for two successive lines, so this should be easy enough.
	my $local_ieb = 0;
	my $local_iib = 0;
	my $local_imb = $hHunk->{masked_start};

	# Count non-elogind block #ifs. This is needed, so normal
	# #if/#else/#/endif constructs can be put inside elogind mask blocks.
	my $regular_ifs = 0;

	# Note down the line numbers where we found #if for quicker access
	my $mask_block_start = -1;

	# We need to know whether to convert an insert line or not
	my $need_endif_conversion = 0;

	# If we leave a note, add the original mask message
	my $mask_message = $EMPTY;

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# entering an elogind mask
		# ---------------------------------------
		empty_handle_mask_start( $line, \$mask_message, \$local_iib, \$local_imb ) and $mask_block_start = $i and next;

		# entering an elogind insert
		# ---------------------------------------
		empty_handle_insert_start( $line, \$mask_message, \$local_ieb, \$local_iib ) and next;

		# Count regular #if
		${$line} =~ m/^-[${HASH}]if/msx and ++$regular_ifs;

		# Switching from Mask to else.
		# Note: Inserts have no #else, they make no sense.
		# ---------------------------------------
		empty_handle_mask_to_else( $line, \$i, \$mask_message, \$mask_block_start, \$local_ieb, \$need_endif_conversion ) and next;

		# ending a Mask block
		# ---------------------------------------
		if ( empty_handle_mask_end( $line, \$i, \$mask_message, \$mask_block_start, \$need_endif_conversion ) > 0 ) {
			$local_ieb = 0;
			$local_imb = 0;
			next;
		}

		# ending an insert block
		# ---------------------------------------
		if ( is_insert_end( ${$line} ) ) {
			$local_iib             = 0;
			$local_ieb             = 0;
			$mask_block_start      = -1;
			$mask_message          = $EMPTY;
			$need_endif_conversion = 0;

			next;
		} ## end if ( is_insert_end( ${...}))

		# end regular #if
		${$line} =~ m/^-[${HASH}]endif/msx and --$regular_ifs;

	} ## end for my $i ( 0 .. $hHunk...)

	return hunk_is_useful();
} ## end sub check_empty_masks

## @brief Validates and processes include directives within a code hunk.
#
#  This subroutine checks for removals and insertions of include directives,
#  handling cases where includes are commented out, moved, or removed in
#  elogind blocks. It ensures that valid include directives are preserved
#  and that undo operations are properly managed.
#
#  @return Returns 1 upon successful completion.
sub check_includes {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Checking includes ...');

	# We must know when "needed by elogind blocks" start
	my $in_elogind_block = 0;

	# The simple undo check will fail, if we do at least one at once.
	# Delay the undoing of the removals until after the hunk was checked.
	my %undos = ();

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		include_handle_removal( $i + 1, ${$line}, \%undos ) and next;                    # 1) Handling of removals of includes we commented out
		include_handle_insertion( $i + 1, ${$line} ) and next;                           # 2) Handling of insertions, not handled by 1)
		( $in_elogind_block > 0 ) and include_handle_elogind( $i + 1, $line ) and next;  # 3) Handling of "needed by elogind" blocks

		# === Other 1 : Look for "needed by elogind" block starts           ===
		# =====================================================================
		if ( ${$line} =~ m/^[${DASH}${SPACE}]\s*\/\/+.*needed\s+(?:by|for)\s+elogind.*/misx ) {
			log_debug( 'Entering elogind include block at line %d', $i + 1 );
			$in_elogind_block = 1;

			# Never remove the block start
			( ${$line} =~ m/^[${DASH}]/msx ) and substr ${$line}, 0, 1, $SPACE;

			# While we are here, we can see to it, that the additional empty
			# line above our marker does not get removed:
			( $i > 0 )
			        and ( $hHunk->{lines}[ $i - 1 ] =~ m/^[${DASH}]\s*$/msx )
			        and substr $hHunk->{lines}[ $i - 1 ], 0, 1, $SPACE;

			next;
		} ## end if ( ${$line} =~ m/^[${DASH}${SPACE}]\s*\/\/+.*needed\s+(?:by|for)\s+elogind.*/misx)

		# === Other 2 : elogind include blocks end, when the first line is  ===
		# ===           found that does not starts with #include            ===
		# =====================================================================
		if ( $in_elogind_block && !( ${$line} =~ m/^[${DASH}${PLUS}${SPACE}]\s*[${HASH}]include\s*/misx ) ) {
			log_debug( 'Leaving elogind include block at line %d', $i + 1 );

			# diff may want to remove the first empty line after our block.
			( ${$line} =~ m/^[${DASH}]\s*$/msx ) and substr ${$line}, 0, 1, $SPACE;

			# Done now...
			$in_elogind_block = 0;
			next;
		} ## end if ( $in_elogind_block...)

		# === Other 3 : Undo all other removals in elogind include blocks   ===
		# =====================================================================
		$in_elogind_block and ( ${$line} =~ m/^[${DASH}]/msx ) and substr ${$line}, 0, 1, $SPACE;

		# Note: Although it looks like all rules are out the window here, all
		#       elogind includes that are handled above, end in a 'next', so
		#       those won't reach here. Actually 'Other 3' would be never
		#       reached with an #include line.

	} ## end for my $i ( 0 .. $hHunk...)

	# Before we can leave, we have to neutralize the %undo lines:
	for my $lId ( keys %undos ) {
		substr $hHunk->{lines}[$lId], 0, 1, $SPACE;
	}

	return 1;
} ## end sub check_includes

## @brief Validates that the logger name matches expected log message formats.
#
#  This subroutine checks if the provided logger name conforms to the allowed
#  log message prefixes. It ensures that only valid logging functions are called,
#  preventing misuse of the logging system.
#
#  @param logger The logger name to validate.
#  @return Returns 1 if the logger is valid, otherwise throws an exception.
sub check_logger {
	my ($logger) = @_;
	if ( defined $logger ) {
		$logger =~ m/^log_(info|warning|error|status|debug|change)$/xms
		        or confess("logMsg() called from wrong sub $logger");
	}
	return 1;
} ## end sub check_logger

## @brief Validates and processes mask and insert blocks within a hunk.
#
#  This subroutine ensures that elogind mask and insert blocks are properly handled
#  within the hunk. It checks for correct block structure, prevents removal of
#  required empty lines before blocks, and adjusts line positions when additions
#  or changes occur near block boundaries. It also manages transitions between
#  mask, insert, and regular code blocks.
#
#  @return Returns 1 on success, or calls hunk_failed on error.
sub check_masks {

	# early exits:
	( defined $hHunk ) or croak('check_masks: hHunk is undef');
	$hHunk->{useful}   or croak('check_masks: Nothing done but hHunk is useless?');

	log_debug('Checking mask flips ...');

	# -----------------------------------------------------------------------
	# --- Check $hHunk for elogind preprocessor masks and additions       ---
	# --- Rules:                                                          ---
	# --- 1) If we need an alternative for an existing systemd code block,---
	# ---    we do it like this: (*)                                      ---
	# ---      #if 0 /// <some comment with the word "elogind" in it>     ---
	# ---        (... systemd code block, unaltered ...)                  ---
	# ---        -> Any change in this block is okay.                     ---
	# ---      #else                                                      ---
	# ---        (... elogind alternative code ...)                       ---
	# ---        -> Any change in this block is *NOT* okay.               ---
	# ---      #endif // 0                                                ---
	# --- 2) If we need an addition for elogind, we do it like this: (*)  ---
	# ---      #if 1 /// <some comment with the word "elogind" in it>     ---
	# ---        (... elogind additional code ...)                        ---
	# ---        -> Any change in this block is *NOT* okay.               ---
	# ---      #endif // 1                                                ---
	# --- (*) : To be able to handle XML content, masking and unmasking   ---
	# ---       can also be done with :                                   ---
	# ---       Masking : "<!-- 0 /// <comment>" and "// 0 -->"           ---
	# ---       Adding  : "<!-- 1 /// <comment> --> and "<!-- // 1 -->"   ---
	# ---       Else    : "<!-- else // 0 -->"                                 ---
	# -----------------------------------------------------------------------

	# Count non-elogind block #ifs. This is needed, so normal
	# #if/#else/#/endif constructs can be put inside elogind mask blocks.
	my $regular_ifs = 0;

	# We have to note down mask starts. If a name revert takes place right in
	# front of a mask start, diff will put it under the mask start, which
	# would place it at the wrong position.
	my $mask_block_start = -1;

	# If a mask block just ended and is followed by insertions, move the mask end.
	# (See Issue #1 and #4)
	my $mask_end_line = -1;

	# If kept/added lines have to be moved from inside or right below our domain
	# blocks, this variable records the line at which they have to be moved.
	my $move_to_line = -1;

	# Note down how this hunk starts before first pruning
	$hHunk->{masked_start} = $in_mask_block && !$in_else_block ? 1 : 0;

	# Now go through all lines and check them
	my $cur_idx = 0;
	while ( $cur_idx < $hHunk->{count} ) {
		my $line = \$hHunk->{lines}[$cur_idx]; ## Shortcut

		# entering an elogind mask
		# ------------------------------------------------------------------------------
		masks_handle_mask_start( \$cur_idx, $line, \$mask_block_start, \$mask_end_line, \$move_to_line ) and next;

		# entering an elogind insert
		# ------------------------------------------------------------------------------
		masks_handle_insert_start( \$cur_idx, $line, \$mask_block_start, \$mask_end_line, \$move_to_line ) and next;

		# Count regular #if
		${$line} =~ m/^-[${HASH}]if/msx and ++$regular_ifs;

		# Switching from Mask to else.
		# Note: Inserts have no #else, they make no sense.
		# ------------------------------------------------------------------------------
		masks_handle_mask_else( \$cur_idx, $line, \$move_to_line ) and next;

		# ending a Mask block
		# ------------------------------------------------------------------------------
		masks_handle_mask_end( \$cur_idx, $line, \$mask_block_start, \$mask_end_line ) and next;

		# ending an insert block
		# ------------------------------------------------------------------------------
		masks_handle_insert_end( \$cur_idx, $line, \$mask_block_start, \$mask_end_line ) and next;

		# end regular #if
		${$line} =~ m/^-[${HASH}]endif/msx and --$regular_ifs;

		# Special treatment for all mask-else and insert blocks.
		# (Well, that's what this function is all about, isn't it?)
		# ------------------------------------------------------------------------------
		masks_sanitize_elogind_blocks( \$cur_idx, $line, \$mask_block_start, \$mask_end_line, \$move_to_line ) and next;

		# Being here means that we are in a mask block or outside of any block.
		# ------------------------------------------------------------------------------
		masks_sanitize_additions( $cur_idx, $line, \$mask_end_line, \$move_to_line );

		++$cur_idx;
	} ## end while ( $cur_idx < $hHunk...)

	# Note down how this hunk ends before first pruning
	$hHunk->{masked_end} = $in_mask_block && !$in_else_block ? 1 : 0;

	return hunk_is_useful();
} ## end sub check_masks

## @brief Checks for musl libc compatibility blocks in a hunk.
#
#  This function identifies and processes #ifdef __GLIBC__ ... #else ... #endif
#  constructs within a code hunk. It handles the conversion of musl-specific
#  blocks by removing the leading '-' from lines that belong to the #else
#  (musl) portion of such blocks, while ensuring proper nesting and state tracking
#  for mask blocks and __GLIBC__ conditional compilation.
#
#  @return Returns 1 on successful processing, 0 if early exit conditions are met.
sub check_musl {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Checking musl libc protection ...');

	# -----------------------------------------------------------------------
	# --- Check for musl_libc compatibility blocks                        ---
	# --- Rules:                                                          ---
	# --- For musl-libc compatibility, there are some                     ---
	# ---   #ifdef __GLIBC__ (...) #else (...) #endif // __GLIBC__        ---
	# --- helpers.                                                        ---
	# --- These can also be "#if ( defined __GLIBC__ )"                      ---
	# --- Note: We handle them like regular mask blocks, because the      ---
	# ---       __GLIBC__ block is considered to be the original, while   ---
	# ---       the musl_libc compat block is the #else block.            ---
	# -----------------------------------------------------------------------

	# Count non-elogind block #ifs. This is needed, so normal
	# #if/#else/#/endif constructs can be put inside both the original
	# and the alternative block.
	my $regular_ifs = 0;

	# Remember the final mask state for later reversal
	# ------------------------------------------------
	my $hunk_ends_in_mask = $in_mask_block;
	my $hunk_ends_in_else = $in_else_block;
	$in_mask_block = $hHunk->{masked_start} ? 1 : 0;
	$in_else_block = 0;

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# The increment/decrement variant can cause negative values:
		validate_block_counters();

		# Quick mask checks, we must have the intermediate states
		# -------------------------------------------------------
		is_mask_start( ${$line} ) and ++$in_mask_block and next;
		if ( is_mask_end( ${$line} ) ) {
			$in_mask_block--;
			$in_else_block--;
			next;
		}

		# entering a __GLIBC__ block as mask
		# ---------------------------------------
		if ( ${$line} =~ m/^-[${HASH}]if(?:def|\s+defined).+__GLIBC__/msx ) {
			## Note: Here it is perfectly fine to be in an elogind mask block.
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'
			$in_glibc_block = 1;
			next;
		} ## end if ( ${$line} =~ m/^-[${HASH}]if(?:def|\s+defined).+__GLIBC__/msx)

		# entering a __GLIBC__ block as insert
		# ---------------------------------------
		if ( ${$line} =~ m/^-[${HASH}]if(?:ndef|\s+!defined).+__GLIBC__/msx ) {
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'
			$in_glibc_block = 1;
			$in_else_block++;
			next;
		} ## end if ( ${$line} =~ m/^-[${HASH}]if(?:ndef|\s+!defined).+__GLIBC__/msx)

		# Count regular #if
		${$line} =~ m/^-[${HASH}]if/msx and ++$regular_ifs;

		# Switching from __GLIBC__ to else
		# ---------------------------------------
		if ( ${$line} =~ m/^[-${SPACE}]?[${HASH}]else\s+[\/]+\s+__GLIBC__/msx ) {
			++$in_else_block;
			substr ${$line}, 0, 1, $SPACE;
			next;
		}

		# ending a __GLBC__ block
		# ---------------------------------------
		if ( ${$line} =~ m/^[${DASH}][${HASH}]endif\s*\/\/\/?.*__GLIBC__/msx ) {
			( !$in_glibc_block )
			        and return hunk_failed('check_musl: #endif // __GLIBC__ found outside any __GLIBC__ block');
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'
			$in_glibc_block = 0;
			$in_else_block--;
			next;
		} ## end if ( ${$line} =~ m/^[${DASH}][${HASH}]endif\s*\/\/\/?.*__GLIBC__/msx)

		# end regular #if
		${$line} =~ m/^-[${HASH}]endif/msx and --$regular_ifs;

		# Remove '-' prefixes in all lines within the musl (#else) blocks
		# -------------------------------------------------------------------
		if (       ( ${$line} =~ m/^[${DASH}]/msx )
			&& ( $in_glibc_block > 0 )
			&& ( $in_else_block > $in_mask_block ) )
		{
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'
		} ## end if ( ( ${$line} =~ m/^[${DASH}]/msx...))
	} ## end for my $i ( 0 .. $hHunk...)

	# Revert the final mask state remembered above
	# ------------------------------------------------
	$in_mask_block = $hunk_ends_in_mask;
	$in_else_block = $hunk_ends_in_else;

	return hunk_is_useful();
} ## end sub check_musl

## @brief Checks for name reversals (elogind<->systemd) within a hunk and handles them appropriately.
#
#  This subroutine analyzes changes in a hunk to identify potential name reversals between elogind and systemd,
#  including tracking mask states, mapping line changes, handling false positives, and processing solo
#  additions/removals. It also manages splicing of lines and protects certain removals from further checks.
#
#  @return Returns 1 on successful completion, 0 if early exit conditions are met (e.g., undefined hunk or not useful).
sub check_name_reverts {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Checking name reversals elogind->systemd ...');

	# Note down what is changed, so we can have inline updates
	my %hChanges = ();
	## {'lines'} => list with line number as index to map changes back to lines
	##          [line_no] => pointer to the change (\$hCHanges{'texts'}{'changes'}[no])
	##                  +--> Meant as a shortcut with write-back functionality
	## {'texts'} => Changes are identified and thus mapped by their core text
	##          {string}    => The string extracted from the line
	##                  {'count'}   => Number of changes recorded
	##                  {'changes'} => The recorded changes list
	##                            [no] => The nth occurance of the string in the hunk
	##                                {'alttxt'}    = Alternative text with elogind<=>systemd flipped
	##                                {'iscomment'} = $TRUE if inside a comment, $FALSE if not.
	##                                {'done'}      = Set to $TRUE once this change has been dealt with, defaults to $FALSE
	##                                {'elogind'}   = 1 if 'kind' is $KIND_ELOGIND or $KIND_LOGINCTL, 0 otherwise
	##                                {'kind'}      = source kind - $KIND_ELOGIND, $KIND_LOGINCTL, $KIND_SYSTEMD, $KIND_SYSTEMCTL (What this 'text' is)
	##                                {'line'}      = line_no where the change took place
	##                                {'masked'}    = $TRUE in mask block, $FALSE not masked or in else block
	##                                {'partner'}   = the type*-1 variant with systemd<=>elogind text replacements or undef if none was found
	##                                {'prev'}      = the previously found entry equaling this. Used to backward chain found partners for a change
	##                                {'spliceme'}  = line_no - The line number to splice (can differ from {line}) or 0 for no splice.
	##                                {'systemd'}   = 1 if 'kind' is $KIND_SYSTEMD or $KIND_SYSTEMCTL, 0 otherwise
	##                                {'text'}      = The text used as {string}, needed for iteration over {'lines'}
	##                                {'type'}      = $TYPE_REMOVAL, $TYPE_ADDITION, $TYPE_NEUTRAL

	# Remember the final mask state for later reversal
	# ------------------------------------------------------------------------------------------------------------
	my $hunk_ends_in_mask = $in_mask_block;
	my $hunk_ends_in_else = $in_else_block;
	$hHunk->{masked_start} and $in_mask_block = 1 or $in_mask_block = 0;

	# The increment/decrement variant can cause negative values
	validate_block_counters();
	$in_else_block = 0;

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line_p = \$hHunk->{lines}[$i]; ## Shortcut
		( defined ${$line_p} )
		        or return hunk_failed( 'check_name_reverts: Line ' . ( $i + 1 ) . "/$hHunk->{count} is undef?" );

		# Quick mask checks, we must have the intermediate states
		# -------------------------------------------------------
		is_mask_start( ${$line_p} ) and ++$in_mask_block and next;
		is_mask_else( ${$line_p} )  and ++$in_else_block and next;
		if ( is_mask_end( ${$line_p} ) ) {
			$in_mask_block = 0;
			$in_else_block = 0;
			next;
		}
		my $is_masked_now = ( ( 0 < $in_mask_block ) && ( 1 > $in_else_block ) ) ? 1 : 0;

		# Analyze basic status of the line
		# -----------------------------------------------------------
		change_analyze_hunk_line( \%hChanges, $i, ${$line_p}, $is_masked_now );
	} ## end for my $i ( 0 .. $hHunk...)

	# Generally there are three types of changes:
	# 1) The simple removal, when there is only one change of type -1
	# 2) The simple addition, when there is only one change of type +1
	# 3) The change where there is an even number of changes with two consecutive being type opposites
	#    ( This can be an addition followed by a removal or a removal followed by an addition. )
	# However, we have to find the counterpart to the change before we can do anything, and for
	# that to work all changes of the hunk have to be recorded first.
	# ------------------------------------------------------------------------------------------------------------
	change_map_hunk_lines( \%hChanges );

	# Before we can process our findings, we have to protect false positives, like mentioning of systemd daemons elogind does not ship.
	# ------------------------------------------------------------------------------------------------------------
	change_handle_false_positives( \%hChanges );

	# Before we can go through our findings, we have to check the solos, meaning additions and removals that have no partner set.
	# Removals are okay, unless they contain an elogind function call.
	# Additions have to be checked for possible systemd->elogind renaming
	# ------------------------------------------------------------------------------------------------------------
	change_check_solo_changes( \%hChanges );

	# Check additions that have not been handled with.
	# ------------------------------------------------------------------------------------------------------------
	change_handle_additions( \%hChanges );

	# Upward removals (where the addition comes first) are handled with last
	# ------------------------------------------------------------------------------------------------------------
	change_handle_removals( \%hChanges );

	# Protect those lines that we allow to be removed, so neither the comment nor func checker will touch them.
	# ------------------------------------------------------------------------------------------------------------
	change_protect_removals( \%hChanges );

	# Splice the lines that were noted for splicing
	# ------------------------------------------------------------------------------------------------------------
	change_splice_the_undone( \%hChanges );

	# Revert the final mask state remembered above
	# ------------------------------------------------------------------------------------------------------------
	$in_mask_block = $hunk_ends_in_mask;
	$in_else_block = $hunk_ends_in_else;

	return hunk_is_useful();
} ## end sub check_name_reverts

## @brief Checks for and handles __STDC_VERSION__ guards in code hunks.
#
#  This function verifies that __STDC_VERSION__ guards are properly handled
#  within a code hunk. It ensures that such guards are not used unconditionally
#  in headers, which can cause issues in C++ builds where the macro is not defined.
#  The function also manages mask block states and handles the removal of guards
#  when paired with appropriate additions.
#
#  @return Returns 1 upon successful completion of the check.
sub check_stdc_version {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Checking __STDC_VERSION__ guards...');

	# -----------------------------------------------------------------------
	# --- Check for __STDC_VERSION__ guards                               ---
	# --- Rules:                                                          ---
	# ---   In some headers __STDC_VERSION__ is used unconditionally.     ---
	# ---   This causes trouble in C++ builds, as that macro is not set   ---
	# ---   there. In elogind this macro is always guarded.               ---
	# -----------------------------------------------------------------------

	# Remember the final mask state for later reversal
	# ------------------------------------------------
	my $hunk_ends_in_mask = $in_mask_block;
	my $hunk_ends_in_else = $in_else_block;
	$in_else_block = 0;
	$in_mask_block = $hHunk->{masked_start} ? 1 : 0;

	# Remember lines directly, as those switches are one-liners only
	my $line_del_num = -1;
	my $line_del_str = $EMPTY;
	my $line_rep_num = -1;
	my $line_rep_str = $EMPTY;
	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# The increment/decrement variant can cause negative values:
		validate_block_counters();

		# Quick mask checks, we must have the intermediate states
		# -------------------------------------------------------
		is_mask_start( ${$line} ) and ++$in_mask_block and next;
		if ( is_mask_end( ${$line} ) ) {
			$in_mask_block--;
			$in_else_block--;
			next;
		}

		# Having a removal of a guardian
		# ---------------------------------------
		if ( ${$line} =~ m/^[${DASH}][${HASH}]\s*if\s+defined[(][_]{2}STDC[_]VERSION[_]{2}[)]\s+&&\s+/msx ) {
			## Note: Here it is perfectly fine to be in an elogind mask block.
			$line_del_num = $i;
			$line_del_str = ${$line};
			next;
		} ## end if ( ${$line} =~ m/^[${DASH}][${HASH}]\s*if\s+defined[(][_]{2}STDC[_]VERSION[_]{2}[)]\s+&&\s+/msx)

		# Having the line without guardian added
		# ---------------------------------------
		if ( ${$line} =~ m/^[${PLUS}][${HASH}]\s*if\s+/msx ) {
			$line_rep_num = $i;
			$line_rep_str = ${$line};
		}

		# If we have a deletion and a fitting addition in the next line,
		# revert the first and remove the second.
		if ( ( $line_del_num > -1 ) && ( ( $line_del_num + 1 ) == $line_rep_num ) && ( $line_rep_str =~ /^[${PLUS}][${HASH}](\s*)if\s+(\S.*)$/msx ) ) {
			my $alt_line = "-#${1}if ( defined __STDC_VERSION__ ) && $2";
			if ( $alt_line eq $line_del_str ) {

				# Yes, the just want to take out the guard.
				# Let's revert that
				substr $hHunk->{lines}[$line_del_num], 0, 1, $SPACE;
				splice @{ $hHunk->{lines} }, $line_rep_num, 1;
				--$hHunk->{count};
			} ## end if ( $alt_line eq $line_del_str)
			$line_del_num = -1;
			$line_rep_num = -1;
		} ## end if ( ( $line_del_num >...))
	} ## end for my $i ( 0 .. $hHunk...)

	# Revert the final mask state remembered above
	# ------------------------------------------------
	$in_mask_block = $hunk_ends_in_mask;
	$in_else_block = $hunk_ends_in_else;

	return hunk_is_useful();
} ## end sub check_stdc_version

## @brief Checks .sym files for unsupported API function uncommenting attempts and corrects them.
#
#  This subroutine processes hunks in .sym.pwx files to detect and handle attempts to uncomment
#  unsupported API function calls. It converts valid function declarations from active to commented
#  form and vice versa/ ensuring that only supported functions are uncommented in the final output.
#  The function operates on additions and removals within the hunk, tracking changes to maintain
#  correct line mapping for potential splicing operations.
#
#  @return Returns 1 on successful processing, or calls hunk_failed on error conditions.
sub check_sym_lines {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	# -----------------------------------------------------------------------
	# --- Check for attempts to uncomment unsupported API functions       ---
	# --- in .sym files.                                                  ---
	# --- In here we change unsupported function calls from               ---
	# ---        sd_foo_func;                                             ---
	# --- to                                                              ---
	# ---        /* sd_foo_func; */                                       ---
	# -----------------------------------------------------------------------

	# Only .sym files are handled here
	$hFile{source} =~ m/[${DOT}]sym[${DOT}]pwx$/msx or return 1;

	log_debug('Checking .sym file sanity...');

	# Note down what is changed, so we can have inline updates
	my %hAdditions = ();
	my %hRemovals  = ();

	# We need a sortable line map for possible later splicing
	my %hAddMap = ();

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		( defined ${$line} )
		        or return hunk_failed( 'check_sym_files: Line ' . ( $i + 1 ) . "/$hHunk->{count} is undef?" );

		# Note down removals
		# ---------------------------------
		if ( ${$line} =~ m/^[${DASH}]\s*\/[${STAR}]\s+(\S.+;)\s+[${STAR}]\/\s*$/msx ) {
			$hRemovals{$1}{line} = $i;
			next;
		}

		# Check Additions
		# ---------------------------------
		if ( ${$line} =~ m/^[${PLUS}]\s*([^${SPACE}\/].+;)\s*$/msx ) {
			$hAdditions{$1}{line}    = $i;
			$hAdditions{$1}{handled} = 0;
			$hAddMap{$i}             = $1;
		}
	} ## end for my $i ( 0 .. $hHunk...)

	# Now we go backwards through the lines that got added and revert the reversals.
	for my $i ( reverse sort { $a <=> $b } keys %hAddMap ) {
		my $item = $hAddMap{$i};

		# First a sanity check against double insertions.
		$hAdditions{$item}{handled}
		        and return hunk_failed( 'check_sym_files: Line' . ( $i + 1 ) . ": Double addition of '$item' found!" );

		# New stuff is in order:
		( defined $hRemovals{$item} ) or ++$hAdditions{$item}{handled} and next;

		# Here we simply undo the removal and splice the addition:
		substr $hHunk->{lines}[ $hRemovals{$item}{line} ], 0, 1, $SPACE;
		( splice @{ $hHunk->{lines} }, $i, 1 );
		$hAdditions{$item}{handled} = 1;
		--$hHunk->{count};
	} ## end for my $i ( reverse sort...)

	return hunk_is_useful();
} ## end sub check_sym_lines

## @brief Checks for and removes useless updates in a hunk.
#
#  This function identifies hunks that perform no actual changes, such as
#  removing and immediately adding the same content. It modifies the hunk
#  in place by splicing out the redundant lines.
#
#  @return Returns 1 on successful completion.
sub check_useless {

	# early exits:
	( defined $hHunk ) or croak('check_useless: hHunk is undef');
	$hHunk->{useful}   or croak('check_useless: Nothing done but hHunk is useless?');

	log_debug('Checking for useless updates...');

	# -----------------------------------------------------------------------
	# --- Check for useless updates that do nothing.                      ---
	# --- The other checks and updates can lead to hunks that effectively ---
	# --- do nothing as they end up like:                                 ---
	# --- -foo                                                            ---
	# --- -bar                                                            ---
	# --- +foo                                                            ---
	# --- +bar                                                            ---
	# -----------------------------------------------------------------------

	# Note down removals, and where they start
	my %hRemovals = ();
	my $r_start   = -1;

	# We later work with an offset, to check for useless changes to splice
	my %hSplices = ();
	my $r_offset = -1;

	# Now go through the line and find out what is to be done
	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# --- (1) Note down removal ---
		if ( ${$line} =~ m/^[${DASH}](.*)$/msx ) {
			my $token = $1 // $EMPTY;
			$token =~ s/\s+$//ms; ## No trailing whitespace/lines!
			$r_start > -1 or $r_start = $i;
			( length $token ) and $hRemovals{$token} = $i
			        or $hRemovals{ 'empty' . $i } = $i;
			next;
		} ## end if ( ${$line} =~ m/^[${DASH}](.*)$/msx)

		# --- (2) Check Addition ---
		if ( ${$line} =~ m/^[${PLUS}](.*)$/msx ) {
			my $token = $1 // $EMPTY;
			$token =~ s/\s+$//ms; ## No trailing whitespace/lines!
			$r_offset > -1 or $r_offset = $i - $r_start;
			if ( ( length $token ) && ( ( defined $hRemovals{$token} ) && ( $hRemovals{$token} + $r_offset ) == $i ) ) {

				# Yep, this has to be reverted.
				substr $hHunk->{lines}[ $i - $r_offset ], 0, 1, $SPACE;
				$hSplices{$i} = 1;
				next;
			} ## end if ( ( length $token )...)
		} ## end if ( ${$line} =~ m/^[${PLUS}](.*)$/msx)

		# --- (3) Reset state on the first out-of-block line
		$r_start   = -1;
		$r_offset  = -1;
		%hRemovals = ();
	} ## end for my $i ( 0 .. $hHunk...)

	# Now go through the splice map and splice from back to front
	for my $line_no ( reverse sort { $a <=> $b } keys %hSplices ) {
		log_debug( "  => Splicing Line %d: '%s'", $line_no, $hHunk->{lines}[$line_no] );
		( splice @{ $hHunk->{lines} }, $line_no, 1 );
		$hHunk->{count}--;
	}

	return hunk_is_useful();
} ## end sub check_useless

## @brief Checks out a specific commit in the upstream repository.
#
#  This subroutine checks out a given commit in the upstream repository. If the
#  commit is not defined or empty, it returns early with success. It first saves
#  the current HEAD commit, then retrieves the shortened hash of the target
#  commit. If the target commit differs from the current one, it performs the
#  checkout operation. Error handling is included for all Git operations.
#
#  @return Returns 1 on successful completion, 0 on failure.
sub checkout_upstream {
	my ($commit) = @_;

	# It is completely in order to not wanting to checkout a specific commit.
	( defined $commit ) and ( length $commit ) or return 1;

	my $new_commit = $EMPTY;
	my $git        = Git::Wrapper->new($upstream_path);
	my @lOut       = ();

	# Save the previous commit
	try {
		@lOut = $git->rev_parse( { short => 1 }, 'HEAD' );
	} catch {
		log_error( "Couldn't rev-parse $upstream_path HEAD\nExit Code : %s\nMessage   : %s", $_->status, $_->error );
		return 0;
	};
	$previous_commit = $lOut[0];

	# Get the shortened commit hash of $commit
	try {
		@lOut = $git->rev_parse( { short => 1 }, $commit );
	} catch {
		log_error( "Couldn't rev-parse %s '%s'\nExit Code : %s\nMessage   : %s", $upstream_path, $commit, $_->status, $_->error );
		return 0;
	};
	$new_commit = $lOut[0];

	# Now check it out, unless we are already there:
	if ( $previous_commit ne $new_commit ) {
		show_progress( 0, 'Checking out %s in upstream tree...', $new_commit );
		try {
			$git->checkout($new_commit);
		} catch {
			log_error( "Couldn't checkout '%s' in %s\nExit Code : %s\nMessage   : %s", $new_commit, $upstream_path, $_->status, $_->error );
			return 0;
		};
		show_progress( 1, 'Checking out %s in upstream tree... done!', $new_commit );
	} ## end if ( $previous_commit ...)

	return 1;
} ## end sub checkout_upstream

## @brief Cleans up the hFile hash by undefining its hunks and resetting counters.
#
#  This subroutine clears all entries in the hFile hash's hunks array, resets the count to zero,
#  and reinitializes the hunks and output arrays to empty references. It ensures that the
#  hFile structure is properly reset for reuse.
#
#  @return Returns 1 to indicate successful completion of the cleanup operation.
sub clean_hFile {
	( defined $hFile{count} ) or return 1;

	for my $i ( $hFile{count} - 1 .. 0 ) {
		( defined $hFile{hunks}[$i] ) and undef %{ $hFile{hunks}[$i] };
	}

	$hFile{count}  = 0;
	$hFile{hunks}  = [];
	$hFile{output} = [];

	return 1;
} ## end sub clean_hFile

## @brief Counts useful hunks in a file and returns the count.
#
# This subroutine iterates through all hunks in a file, checks if each hunk is
# useful using the hunk_is_useful() function. If a hunk is deemed useful,
# it's pruned with prune_hunk() and counted as a useful hunk.
# The count of useful hunks is returned at the end of the iteration.
#
#  @return Returns the number of useful hunks found in the file.
sub count_useful_hunks {
	my $have_hunk = 0;
	for my $pos ( 0 .. $hFile{count} - 1 ) {
		$hHunk = $hFile{hunks}[$pos]; ## Global shortcut

		# (pre -> early out)
		hunk_is_useful() or next;

		prune_hunk() and ++$have_hunk;
	} ## end for my $pos ( 0 .. $hFile...)

	return $have_hunk;
} ## end sub count_useful_hunks

## @brief Handles program termination with error logging and exception throwing.
#
#  This subroutine sets global variables to indicate program death and logs the
#  provided error message before throwing a fatal exception using confess.
#
#  @param err The error message to be logged.
#  @return This subroutine does not return as it calls confess which exits the program.
sub dieHandler {
	my ($err) = @_;

	$death_note = 5;
	$ret_global = 42;

	log_error( '%s', $err );

	confess('Program died');
} ## end sub dieHandler

## @brief Generate unified diff for header files with pre-processing support.
#
#  This subroutine generates a unified diff between source and target files,
#  performing necessary preprocessing steps based on file type. It handles
#  shell scripts and XML files by unmasking special characters and preparing
#  the files for comparison. For new files, it skips preprocessing steps.
#  The diff output is formatted to show relative paths and handles creation
#  of new files appropriately.
#
#  @return Returns 1 on successful completion, 0 on error.
sub diff_hFile {

	# If this is not an attempt to create a new file, a few preparations
	# and checks can be made beforehand. They make no sense on new files.
	if ( 0 == $hFile{create} ) {

		# Do they differ at all?
		my $r;
		$r = `diff -qu "$hFile{source}" "$hFile{target}" 1>/dev/null 2>&1`;
		$? or return 0;

		# Shell and meson files must be prepared. See prepare_meson()
		$hFile{is_sh} and $hFile{pwxfile} = 1 and prepare_shell();

		# We mask double dashes in XML comments using XML hex entities. These
		# must be unmasked for processing.
		$hFile{is_xml} and $hFile{pwxfile} = 1 and prepare_xml();
	} ## end if ( 0 == $hFile{create...})

	# Let's have three shortcuts:
	my $src = $hFile{source};
	my $tgt = $hFile{target};
	my $prt = $hFile{part};

	# Now the diff can be built ...
	my @lDiff = `diff -N -u "$src" "$tgt"`;

	# ... the head of the output can be generated ...
	@{ $hFile{output} } = splice @lDiff, 0, 2;
	chomp $hFile{output}[0];                                             # These now have absolute paths, and source meson files have a
	chomp $hFile{output}[1];                                             # .pwx extensions. That is not what the result shall look like.
	$hFile{create}                                                       # But we have $hFile{part}, which is already the
	        and $hFile{output}[0] =~ s/$src/${SLASH}dev${SLASH}null/msx  # relative file name of the file we are
	        or $hFile{output}[0]  =~ s/$src/a${SLASH}$prt/msx;           # processing, and we know if a file is
	$hFile{output}[1] =~ s/$tgt/b${SLASH}$prt/ms;                        # to be created.

	# ... and the raw hunks can be stored.
	my $max_idx = ( scalar @lDiff ) - 1;
	my $cur_idx = 1;
	while ( $cur_idx < $max_idx ) {
		if ( $ATAT eq ( substr $lDiff[$cur_idx], 0, 2 ) ) {
			build_hHunk( splice @lDiff, 0, $cur_idx ) or return 0;
			$max_idx -= $cur_idx;
			$cur_idx = 1; ## Start at 1 or we crash at going for '@@' again.
			next;
		} ## end if ( $ATAT eq ( substr...))
		++$cur_idx;
	} ## end while ( $cur_idx < $max_idx)
	scalar @lDiff and build_hHunk(@lDiff);

	return 1;
} ## end sub diff_hFile

## @brief Performs pre-checks for the tree operation.
#
#  This subroutine validates the command-line options and file arguments before proceeding
#  with the tree operation. It ensures that --create is not used on the full tree,
#  --stay is used with a commit option, and all specified files exist unless --create
#  is used to create them.
#
#  @return Returns 1 if all pre-checks pass, 0 otherwise.
sub do_prechecks {
	my $result = 1;

	# If --create was given, @wanted_files must not be empty
	if ( $result && !$show_help && $do_create && ( 0 == scalar @wanted_files ) ) {
		print "ERROR: --create must not be used on the full tree!\n";
		print "       Add at least one file using the --file option.\n";
		$result = 0;
	}

	# If --stay was given, $wanted_commit must not be empty
	if ( $result && !$show_help && $do_stay && ( 0 == ( length $wanted_commit ) ) ) {
		print "ERROR: --stay makes only sense with the -c|--commit option!\n";
		$result = 0;
	}

	# If any of the wanted files do not exist, error out unless --create was used.
	if ( $result && !$show_help && ( defined $wanted_files[0] ) ) {
		foreach my $f (@wanted_files) {
			-f $f
			        or $do_create and $hToCreate{$f} = 1
			        or print "ERROR: $f does not exist!\n" and $result = 0;
		}
	} ## end if ( $result && !$show_help...)

	return $result;
} ## end sub do_prechecks

## @brief Handles empty mask end line processing and re-enables removed lines when conditions are met.
#
#  This subroutine processes a given line to check if it's the end of a mask (using is_mask_end).
#  If the line is indeed an end of a mask, it checks various conditions related to the position
#  of the line within the hunk and whether certain conversions need to be made.
#
#  When the endif follows immediately after the mask start and there's sufficient space in the patch,
#  it re-enables removed lines (marked with DASH) and adds a comment indicating the empty mask removal.
#  If an endif conversion is needed, it also handles that by adding the appropriate endif line.
#
#  The function updates various references to track the state of the hunk being processed.
#
#  @param $line Reference to the current line string being checked
#  @param $line_no_p Pointer/reference to the current line number in the hunk
#  @param $message_p Pointer/reference to store messages about the processing
#  @param $mask_block_start_p Pointer/reference to track the start of mask block
#  @param $need_conversion_p Pointer/reference indicating if conversion is needed
#  @return Returns 1 if the line was processed as a mask end, otherwise returns 0
sub empty_handle_mask_end {
	my ( $line, $line_no_p, $message_p, $mask_block_start_p, $need_conversion_p ) = @_;

	if ( is_mask_end($line) ) {
		my $i = ${$line_no_p};

		# If the endif is right after the mask start, we have to do something about it, but only if we have enough space left in the patch
		if ( $i < ( $hHunk->{count} - 2 ) ) {
			if ( $i && ( $i == ( ${$mask_block_start_p} + 1 ) ) ) {

				# Re-enable the removal of the "#if 0" and of the "#endif" line
				substr $hHunk->{lines}[ $i - 1 ], 0, 1, "${DASH}";
				substr $hHunk->{lines}[$i],       0, 1, "${DASH}";

				# Add a note that we converted this
				splice @{ $hHunk->{lines} }, $i + 1, 0,
				        ( ${PLUS} . ( $hFile{is_sh} ? "${HASH}${SPACE}" : $EMPTY ) . "/// elogind empty mask removed (${$message_p})" );

				$hHunk->{count} += 1;
			} ## end if ( $i && ( $i == ( $...)))

			# If we need an endif conversion, do it now:
			elsif ( ${$need_conversion_p} > 0 ) {

				# First re-enable the removal:
				substr $hHunk->{lines}[$i], 0, 1, "${DASH}";

				# Add the correct endif
				splice @{ $hHunk->{lines} }, $i + 1, 0, ('+#endif // 1');

				$hHunk->{count} += 1;
				${$line_no_p}   += 1; ## Already known...
			} ## end elsif ( ${$need_conversion_p...})
		} ## end if ( $i < ( $hHunk->{count...}))

		${$mask_block_start_p} = -1;
		${$message_p}          = $EMPTY;
		${$need_conversion_p}  = 0;

		return 1;
	} ## end if ( is_mask_end($line...))

	return 0;

} ## end sub empty_handle_mask_end

## @brief Handles empty mask to "else" conversion for line processing.
#
# This subroutine processes lines where an "else" statement follows immediately after
# a masked code section. If certain conditions are met, it modifies the mask to handle
# this scenario correctly by adjusting the patch and adding appropriate notes.
# The purpose is to ensure proper handling of empty mask blocks that end with an else
# statement, preserving the integrity of the code transformation process.
#
# @param line Reference to a string containing the current line being processed.
# @param line_no_p Reference to an integer indicating the current line number in the patch.
# @param message_p Reference to a string used for logging or messaging purposes.
# @param mask_block_start_p Reference to an integer indicating where the mask block starts.
# @param is_else_begin_p Reference to a flag indicating if this is the beginning of an else block.
# @param need_conversion_p Reference to a flag indicating whether conversion was needed.
# @return Returns 1 if the line was processed as an empty mask followed by an "else", 0 otherwise.
sub empty_handle_mask_to_else {
	my ( $line, $line_no_p, $message_p, $mask_block_start_p, $is_else_begin_p, $need_conversion_p ) = @_;

	if ( is_mask_else( ${$line} ) ) {
		my $i = ${$line_no_p};
		${$is_else_begin_p} = 1;

		# If the else starts right after a mask start, we have to do something about it, if there is enough space left in the patch
		# (Which should be the case as the else block would have lengthened it. But better check it to be safe!)
		if ( $i && ( $i == ( ${$mask_block_start_p} + 1 ) ) && ( $i < ( $hHunk->{count} - 2 ) ) ) {

			# Re-enable the removal of the "#if 0" and of the "#else" line
			substr $hHunk->{lines}[ $i - 1 ], 0, 1, "${DASH}";
			substr $hHunk->{lines}[$i],       0, 1, "${DASH}";

			# Add a note that we converted this and add an insert mask
			splice @{ $hHunk->{lines} }, $i + 1, 0, ( '+/// elogind empty mask else converted', "+#if 1 /// ${$message_p}" );

			$hHunk->{count} += 2;
			${$need_conversion_p} = 1;
			${$line_no_p} += 2; ## Already known...
		} ## end if ( $i && ( $i == ( $...)))

		${$mask_block_start_p} = -1;

		return 1;
	} ## end if ( is_mask_else( ${$line...}))

	return 0;
} ## end sub empty_handle_mask_to_else

## @brief Handles mask start for empty lines and updates flags accordingly.
#
#  This subroutine checks if the given line indicates the start of a mask
#  section. If it does, it sets relevant flags to indicate that we're starting
#  a mask rather than an insert, and captures any associated message.
#  The is_mask_start() function should have already validated this context,
#  so no additional checks are performed here. This avoids potential issues
#  with later pruning operations modifying the conditions.
#
#  @param line Reference to the line string being checked.
#  @param message_p Reference to store the mask message if found.
#  @param is_insert_begin_p Reference to flag indicating insert start (set to 0 if mask).
#  @param is_mask_begin_p Reference to flag indicating mask start (set to 1 if mask).
#  @return Returns 1 if a mask start was detected, otherwise returns 0.
sub empty_handle_mask_start {
	my ( $line, $message_p, $is_insert_begin_p, $is_mask_begin_p ) = @_;

	if ( is_mask_start( ${$line} ) ) {

		# No checks needed, check_masks() already did that, and later pruning might make
		# checks here fail, if large else block removals got reverted and the hunk(s) pruned.
		${$is_insert_begin_p} = 0;
		${$is_mask_begin_p}   = 1;

		# Note down mask message in case we leave a message
		${$line} =~ m/[${SLASH}]{3}\s*(.+)\s*$/msx and ${$message_p} = $1;

		return 1;
	} ## end if ( is_mask_start( ${...}))

	return 0;
} ## end sub empty_handle_mask_start

## @brief Checks if current line is an insert start and updates flags accordingly
#
# This subroutine checks whether the given line matches the criteria for being an
# "insert start". If it does, it sets appropriate flags to indicate this condition,
# and extracts any message from the line. It returns 1 if a match is found, otherwise 0.
#
# @param $line Reference to the current line string being processed
# @param $message_p Reference to store extracted message (if any)
# @param $is_else_begin_p Reference to flag indicating start of an 'else' section
# @param $is_insert_begin_p Reference to flag indicating start of an 'insert' section
# @return Returns 1 if the line matches insert start criteria, otherwise returns 0
sub empty_handle_insert_start {
	my ( $line, $message_p, $is_else_begin_p, $is_insert_begin_p ) = @_;

	if ( is_insert_start( ${$line} ) ) {
		${$is_insert_begin_p} = 1;
		${$is_else_begin_p}   = 0;

		# Note down mask message in case we leave a message
		${$line} =~ m/[${SLASH}]{3}\s*(.+)\s*$/msx and ${$message_p} = $1;

		return 1;
	} ## end if ( is_insert_start( ...))

	return 0;
} ## end sub empty_handle_insert_start

## @brief This subroutine processes hunks of file data to filter out non-useful ones and applies changes to include statements.
#
#  The finish_hunks subroutine iterates through all hunks in a file. For each hunk,
#  it first checks if the hunk is useful using the hunk_is_useful() function, and skips
#  any non-useful hunks. Then, for potentially useful hunks, it applies changes related to
#  include statements through check_includes(). If after applying these changes a hunk remains
#  non-useful, it is also skipped.
#
#  @return The subroutine returns 1 upon completion of processing all hunks.
sub finish_hunks {
	for my $pos ( 0 .. $hFile{count} - 1 ) {
		$hHunk = $hFile{hunks}[$pos]; ## Global shortcut

		# === 1) useful or early out ======================================
		hunk_is_useful() or next;

		# === 2) Apply what we learned about changed includes =============
		check_includes() and hunk_is_useful() or next;

	} ## end for my $pos ( 0 .. $hFile...)

	return 1;
} ## end sub finish_hunks

sub format_caller {
	my ($caller) = @_;
	$caller =~ s/^.*::([^:]+)$/$1/xms;
	$caller =~ m/__ANON__/xmsi and $caller = 'AnonSub';
	return $caller;
} ## end sub format_caller

## @brief Generates a list of files to check by searching predefined directories and handling user-provided files.
#
#  This function performs initial cleanup by removing temporary files and builds a hash of wanted files
#  from the @wanted_files array. It then uses File::Find to traverse specific directories and root files,
#  ensuring that only relevant files are included in the final list. Files with systemd/elogind alternatives
#  are handled appropriately, and any manually specified files to be created are added to the list.
#
#  @return Returns 1 on success, or 0 if no source files were found.
sub generate_file_list {

	# Do some cleanup first. Just to be sure.
	my $r;
	$r = qx{rm -rf build*};
	$r = qx{find -iname '*.orig' -or -iname '*.bak' -or -iname '*.rej' -or -iname '*~' -or -iname '*.gc??' | xargs rm -f};

	# Build wanted files hash
	while ( my $want = shift @wanted_files ) {
		$have_wanted                                = 1;
		$want =~ m/^[${DOT}][${SLASH}]/msx or $want = "./$want";
		$hWanted{$want}                             = 1;
		$want =~ s/elogind/systemd/msg;
		$hWanted{$want} = 1;
	} ## end while ( my $want = shift ...)

	# The idea now is, that we use File::Find to search for files
	# in all legal directories this program allows. Checking against
	# the built %hWanted ensures that a user provided list of files
	# is heeded.
	for my $xDir ( 'doc', 'docs', 'factory', 'm4', 'man', 'po', 'shell-completion', 'src', 'tools' ) {
		if ( -d "$xDir" ) {
			find( \&wanted, "$xDir" );
		}
	}

	# There are a few root files we need to check, too
	for my $xFile ( 'configure', 'Makefile', 'meson.build', 'meson_options.txt' ) {
		if ( -f "$xFile" ) {
			find( \&wanted, "$xFile" );
		}
	}

	# If the user wants to check files, that do not show up when
	# searching our predefined set of directories, then let them.
	for my $xFile ( keys %hWanted ) {

		# Files with systemd<->elogind alternatives might not be there
		-f "$xFile" or $hWanted{$xFile} = 2;
		$hWanted{$xFile} == 2 and next; ## Already handled or unavailable
		find( \&wanted, "$xFile" );
	} ## end for my $xFile ( keys %hWanted)

	# All files that shall be created must be added manually now.
	scalar keys %hToCreate and push @source_files, keys %hToCreate;

	# Just to be sure...
	scalar @source_files
	        or log_error('No source files found? Where the hell are we?')
	        and return 0;

	# Get the maximum file length and build $file_fmt
	my $mlen = 0;
	for my $f (@source_files) {
		( length $f ) > $mlen and $mlen = ( length $f );
	}
	$file_fmt = sprintf '%%-%d%s', $mlen, 's';

	return 1;
} ## end sub generate_file_list

## @brief Calculates and returns the hunk header line for a diff.
#
#  This function processes the lines within a hunk to determine the start positions
#  and lengths of the source and target sections. It optionally adjusts an offset
#  reference based on the difference in line counts between source and target.
#
#  @param offset Optional reference to adjust the target start position based on
#                line count differences.
#  @return Formatted hunk header string in the format "@@ -src_start,src_len +tgt_start,tgt_len @@"
sub get_hunk_head {
	my ($offset) = @_;

	my $src_len   = 0;
	my $tgt_len   = 0;
	my $lCount    = $hHunk->{count};
	my $src_start = $hHunk->{src_start};
	my $tgt_start = ( defined $offset ) ? $src_start + ${$offset} : $hHunk->{tgt_start};

	for my $i ( 0 .. $lCount - 1 ) {
		if ( $hHunk->{lines}[$i] =~ m/^[${PLUS}]/msx ) {
			$tgt_len++;
		} elsif ( $hHunk->{lines}[$i] =~ m/^[${DASH}]/msx ) {
			$src_len++;
		} else {
			$src_len++;
			$tgt_len++;
		}
	} ## end for my $i ( 0 .. $lCount...)

	# If an offset reference was given, add back the size diff
	( defined $offset )
	        and ${$offset} += $tgt_len - $src_len;

	return sprintf '%s -%d,%d +%d,%d %s', $ATAT, $src_start, $src_len, $tgt_start, $tgt_len, $ATAT;
} ## end sub get_hunk_head

## @brief Generates a formatted location string for log messages based on caller information.
#
#  This subroutine determines the appropriate caller information to include in a log message,
#  considering debug mode and whether the log is from a regular logging function. It formats
#  the caller details using helper functions and returns a string with the location information.
#
#  @param lvl The log level of the message the location is for.
#  @return Formatted location string or empty string if location is not needed.

sub get_location {
	my ($lvl) = @_;

	# The location is not needed in regular info and status messages, unless debug mode is on
	if ( ( 0 == $do_debug ) && ( ( $LOG_INFO == $lvl ) || ( $LOG_STATUS == $lvl ) ) ) {
		return $EMPTY;
	}

	my $is_regular_log   = 0;
	my $curr_caller_line = ( caller 1 )[2] // -1;
	my $curr_caller_name = format_caller( ( caller 2 )[3] // 'main' );
	my $prev_caller_line = ( caller 2 )[2] // -1;
	my $prev_caller_name = format_caller( ( caller 3 )[3] // 'main' );

	( 'main::logMsg' eq ( caller 1 )[3] // 'undef' ) and check_logger($curr_caller_name) and $is_regular_log = 1;

	my $connect_string   = $EMPTY;
	my $line_format      = $EMPTY;
	my $prev_info_format = $EMPTY;
	my @args             = ();

	if ( 1 == $is_regular_log ) {
		$line_format = make_location_fmt( $prev_caller_line, ( length $prev_caller_name ) );

		# Curr is the logging function, prev is the function that does the logging
		( $prev_caller_line > -1 ) and push @args, $prev_caller_line;
		push @args, $prev_caller_name;

	} else {
		$connect_string   = ' called from ';
		$line_format      = make_location_fmt( $curr_caller_line, ( length $curr_caller_name ) );
		$prev_info_format = make_location_fmt( $prev_caller_line, ( length $prev_caller_name ) );

		# curr is the function that calls the sub that logs, and prev is its caller
		( $curr_caller_line > -1 ) and push @args, $curr_caller_line;
		push @args, $curr_caller_name;
		( $prev_caller_line > -1 ) and push @args, $prev_caller_line;
		push @args, $prev_caller_name;
	} ## end else [ if ( 1 == $is_regular_log)]

	my $format_string = $line_format . $connect_string . $prev_info_format;

	return sprintf $format_string, @args;
} ## end sub get_location

## @brief Returns a string representation of the given log level.
#
#  This subroutine maps numeric log level constants to their corresponding
#  string representations for logging purposes. It checks the input level
#  against predefined constants and returns an appropriate label.
#
#  @param level The log level to get the representation string for.
#  @return A string representing the log level: '--Info--', 'Warning!', 'ERROR !!',
#          '-status-', '_DEBUG!_', or '=DEBUG='.
sub get_log_level {
	my ($level) = @_;

	           ( $LOG_INFO == $level )    and return ('--Info--')
	        or ( $LOG_WARNING == $level ) and return ('Warning!')
	        or ( $LOG_ERROR == $level )   and return ('ERROR !!')
	        or ( $LOG_STATUS == $level )  and return ('-status-')
	        or return ('_DEBUG!_');

	return ('=DEBUG=');
} ## end sub get_log_level

sub get_date_now {
	my @tLocalTime = localtime;
	return sprintf '%04d-%02d-%02d', $tLocalTime[5] + 1900, $tLocalTime[4] + 1, $tLocalTime[3];
}

sub get_time_now {
	my @tLocalTime = localtime;
	return sprintf '%04d-%02d-%02d %02d:%02d:%02d', $tLocalTime[5] + 1900, $tLocalTime[4] + 1, $tLocalTime[3], $tLocalTime[2], $tLocalTime[1], $tLocalTime[0];
}

## @brief Records a failed hunk during file processing.
#
#  This subroutine logs information about a failed hunk, including its context and error message.
#  It stores the hunk data, metadata, and the failure reason in the @lFails array for later reporting.
#  The progress line is updated to indicate the failure.
#
#  @param msg The error message describing the hunk failure.
#  @return Always returns 0 to indicate the operation completed with a failure.
sub hunk_failed {
	my ($msg) = @_;
	my $num = scalar @lFails;

	# Generate entry:
	push @lFails, {
		hunk => [get_hunk_head],
		info => {
			count        => $hHunk->{count},
			idx          => $hHunk->{idx},
			masked_end   => $hHunk->{masked_end},
			masked_start => $hHunk->{masked_start},
			offset       => $hHunk->{offset},
			src_start    => $hHunk->{src_start},
			tgt_start    => $hHunk->{tgt_start},
			useful       => $hHunk->{useful}
		},
		msg  => $msg,
		part => $hFile{part}
	        };

	# Add the hunk itself
	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		push @{ $lFails[$num]{hunk} }, $hHunk->{lines}[$i];
		log_debug( '% 3d: %s', $i + 1, $hHunk->{lines}[$i] );
	}

	# And terminate the progress line:
	show_progress( 1, "$file_fmt : %s", $hFile{part}, $msg );

	return 0;
} ## end sub hunk_failed

## @brief Checks whether a hunk is still useful by examining its lines for changes.
#
#  This function determines if a hunk remains useful by checking if it contains any
#  lines that start with '-' or ${PLUS}, indicating additions or deletions. It also
#  updates the hunk's 'useful' flag accordingly. Debug information is logged to
#  track the process and optionally display the lines of useful hunks.
#
#  @return Returns 1 if the hunk is still useful (contains changes), 0 otherwise.
sub hunk_is_useful() {

	# early exits:
	( $death_note > 0 ) and return 0;
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Checking whether the hunk is still useful:');
	log_debug( ' => Mask   Start: in_mask: %d ; in_else: %d ; in_insert: %d', $in_mask_block, $in_else_block, $in_insert_block );

	# See whether at least one change is still present
	my $is_useful = ( defined first { m/^[${DASH}${PLUS}]/msx } @{ $hHunk->{lines} } ) ? 1 : 0;

	$hHunk->{useful} = $is_useful;
	log_debug( '  => Hunk is %s useful', ( $is_useful > 0 ) ? 'still' : 'no longer' );

	( $is_useful > 1 ) and prune_hunk();

	if ( ( $do_debug > 0 ) && ( $is_useful > 0 ) ) {
		for my $i ( 0 .. $hHunk->{count} - 1 ) {
			log_info( '% 3d: %s', $i + 1, $hHunk->{lines}[$i] );
		}
	}

	return $is_useful;
} ## end sub hunk_is_useful

## @brief This subroutine initializes sanity check values for inclusion checks.
#
#  This function iterates over all keys in the %hIncs hash and ensures that certain
#  nested hashes are defined with default values. It resets the 'applied' status
#  to 0, sets up default structures for 'elogind', 'insert', and 'remove'
#  operations if they are not already defined.
#
#  @return Returns 1 after completing the initialization process.
sub include_check_sanity {
	for my $inc ( keys %hIncs ) {
		$hIncs{$inc}{applied} = 0;
		( defined $hIncs{$inc}{elogind} )
		        or $hIncs{$inc}{elogind} = { hunkid => -1, lineid => -1 };
		( defined $hIncs{$inc}{insert} )
		        or $hIncs{$inc}{insert} = { elogind => 0, hunkid => -1, lineid => -1, spliceme => 0, sysinc => 0 };
		( defined $hIncs{$inc}{remove} )
		        or $hIncs{$inc}{remove} = { hunkid => -1, lineid => -1, sysinc => 0 };
	} ## end for my $inc ( keys %hIncs)

	return 1;
} ## end sub include_check_sanity

## @brief Handles "needed by elogind" blocks in include lines.
#
#  This subroutine processes a specific line to handle include directives that
#  are marked as needed by elogind. It checks if the current line matches an
#  expected pattern, and if so, it ensures that the include is not removed.
#  If the include has already been handled or doesn't match the pattern, it returns
#  appropriate values to indicate success or failure in processing.
#
#  The function works by checking if the line contains a specific include pattern,
#  then verifying if this include has been marked for elogind. If the include is
#  found and not previously handled, it removes any marking that would cause it
#  to be removed, ensuring the include remains in the final output.
#
#  @return Returns 0 if the line is not handled by this subroutine or if an error occurs,
#          otherwise returns 1 indicating successful processing of the include insertion.
sub include_handle_elogind {
	my ( $line_no, $line ) = @_;
	my ( $pre, $inc, $post ) = ( $EMPTY, $EMPTY, $EMPTY );

	# === Ruleset 3 : Handling of "needed by elogind" blocks            ===
	# =====================================================================
	if ( ${$line} =~ m/^[${DASH}]\s*[${HASH}]include\s+([<"'])([^>"']+)([>"'])/msx ) {
		( $pre, $inc, $post ) = ( $1, $2, $3 );
	}

	( 0 < ( length $inc ) ) or return 0;         # Not the right line for this handling
	( $hIncs{$inc}{applied} > 0 ) and return 1;  # Correct line, but handled already

	log_debug( 'Checking remove elogind   at % 3d: %s%s%s', $line_no, $pre, $inc, $post );

	# Pre: Sanity check:
	( defined $hIncs{$inc}{elogind}{hunkid} ) and $hIncs{$inc}{elogind}{hunkid} > -1 or return hunk_failed('check_includes: Unrecorded elogind include found!');

	# As 1 and 2 do not apply, simply undo the removal.
	substr ${$line}, 0, 1, $SPACE;
	$hIncs{$inc}{applied} = 1;

	return 1;
} ## end sub include_handle_elogind

## @brief Handles the insertion of include statements in a line.
#
#  This subroutine processes lines that contain include statement insertions not handled by another ruleset. It checks if an include is present and processes it accordingly.
#  If the include is valid, it marks it as applied and returns success. Otherwise, it handles errors appropriately.
#
#  The subroutine first checks if a line contains a specific pattern of include insertion.
#  If found, it extracts the relevant parts (pre, include path, post).
#  It verifies that the extracted include is non-empty and hasn't been processed before.
#  A debug log entry is made for tracking purposes.
#  The subroutine then performs sanity checks to ensure the inclusion has been recorded properly,
#  marks the include as applied in the hash table, and returns success.
#
#  @param line_no Line number of the current line being checked.
#  @param line Reference to a string containing the current line content.
#  @return Returns 0 if the line is not handled by this subroutine or if an error occurs,
#          otherwise returns 1 indicating successful processing of the include insertion.
sub include_handle_insertion {
	my ( $line_no, $line ) = @_;
	my ( $pre, $inc, $post ) = ( $EMPTY, $EMPTY, $EMPTY );

	# === Ruleset 2 : Handling of insertions, not handled by 1          ===
	# =====================================================================
	if ( $line =~ m/^[${PLUS}]\s*[${HASH}]include\s+([<"'])([^>"']+)([>"'])/msx ) {
		( $pre, $inc, $post ) = ( $1, $2, $3 );
	}

	( 0 < ( length $inc ) ) or return 0;         # Not the right line for this handling
	( $hIncs{$inc}{applied} > 0 ) and return 1;  # Correct line, but handled already

	log_debug( 'Checking adding new       at % 3d: %s%s%s', $line_no, $pre, $inc, $post );

	# Pre: Sanity check:
	( defined $hIncs{$inc}{insert}{hunkid} ) and ( $hIncs{$inc}{insert}{hunkid} > -1 ) or return hunk_failed('check_includes: Unrecorded insertion found!');

	# Nicely enough we are already set here.
	$hIncs{$inc}{applied} = 1;

	return 1;
} ## end sub include_handle_insertion

## @brief Processes removal of include statements from source code.
#
#  This subroutine handles various scenarios for removing include statements
#  that were previously commented out. It checks if an include has been
#  removed, whether it was originally inserted by the script or manually,
#  and takes appropriate actions based on its findings:
#
#  - Verifies if the removal is of an obsolete include.
#  - Checks if the removal undoes a previous comment-out action.
#  - Handles cases where includes might have moved or changed type.
#
#  @param $line_no Current line number being processed
#  @param $line Content of the current line
#  @param $undos Reference to hash storing undo actions for lines
#  @return Returns 1 on successful processing, 0 otherwise
sub include_handle_removal {
	my ( $line_no, $line, $undos ) = @_;
	my ( $pre,     $inc,  $post )  = ( $EMPTY, $EMPTY, $EMPTY );

	# === Ruleset 1 : Handling of removals of includes we commented out ===
	# =====================================================================
	if ( $line =~ m/^[${DASH}]\s*\/[${SLASH}${STAR}]+\s*[${HASH}]include\s+([<"'])([^>"']+)([>"'])/msx ) {
		( $pre, $inc, $post ) = ( $1, $2, $3 );
	}

	( 0 < ( length $inc ) ) or return 0;         # Not the right line for this handling
	( $hIncs{$inc}{applied} > 0 ) and return 1;  # Correct line, but handled already

	log_debug( 'Checking remove commented at % 3d: %s%s%s', $line_no, $pre, $inc, $post );

	# Pre: Sanity check:
	my $hInc = $hIncs{$inc};                     # Shortcut
	my $hIns = $hInc->{insert};                  # Shortcut, too
	my $hRem = $hInc->{remove};                  # Shortcut, three

	( defined $hRem->{hunkid} ) and $hRem->{hunkid} > -1
	        or return hunk_failed('check_includes: Unrecorded removal found!');

	log_debug( '    Removal  in hunk %d at line %d', $hRem->{hunkid}, $hRem->{lineid} );
	log_debug( '    Addition in hunk %d at line %d', $hIns->{hunkid}, $hIns->{lineid} );

	# a) Check for removals of obsolete includes.
	#    If no insert was found, then the include was removed by systemd devs for good.
	# ---------------------------------------------------------------------------------------------
	if ( ( $hInc->{elogind}{hunkid} + $hIns->{hunkid} ) < -1 ) {
		log_debug(' => No insertion found, removed by systemd devs.');
		++$hInc->{applied};
		return 1;
	}

	# b) Check for a simple undo of our commenting out
	# ---------------------------------------------------------------------------------------------
	if ( ( $hIns->{hunkid} == $hRem->{hunkid} ) && ( $hIns->{sysinc} == $hRem->{sysinc} ) ) {
		my $ins_diff  = $hIns->{lineid} - $hRem->{lineid};
		my $all_same  = 1;
		my $direction = $ins_diff > 0 ? 1 : -1;
		my $i         = $line_no - 1;
		my $j         = $direction;

		log_debug( ' => Checking undos in %d distance with %d direction', $ins_diff, $direction );

		# Let's see whether there are undos between this and its addition
		# in the same order, meaning there has been no resorting.
		while ( ( $all_same > 0 ) && ( ( abs $j ) < ( abs $ins_diff ) ) ) {
			$all_same = 0;

			if (       ( $hHunk->{lines}[ $i + $j ] =~ m/^[${DASH}]\s*\/[${SLASH}${STAR}]+\s*[${HASH}]include\s+[<"']([^>"']+)[>"']\s*(?:[${STAR}]\/)?/msx )
				|| ( $hHunk->{lines}[ $i + $j ] =~ m/^[${PLUS}]\s*[${HASH}]include\s+[<"']([^>"']+)[>"']/msx ) )
			{
				my $hI = $hIncs{$1}{insert};
				my $hR = $hIncs{$1}{remove};

				log_debug( ' => Comparing Hunk %d line %d sysinc %d "%s"', $hI->{hunkid}, $hI->{lineid}, $hI->{sysinc}, $1 );
				log_debug( ' =>      With Hunk %d line %d sysinc %d "%s"', $hR->{hunkid}, $hR->{lineid}, $hR->{sysinc}, $1 );
				            $hI->{hunkid} == $hR->{hunkid}
				        and $ins_diff == ( $hI->{lineid} - $hR->{lineid} )
				        and $hI->{sysinc} == $hR->{sysinc}
				        and $all_same = 1;
				log_debug( ' They are %s same', $all_same > 0 ? 'the' : 'NOT the' );
			} ## end if ( ( $hHunk->{lines}...))

			$j += $direction;
		} ## end while ( ( $all_same > 0 )...)

		if ( $all_same > 0 ) {

			# The insertion is right before or after the removal. That's pointless.
			log_debug( ' => Undo useless removal, undo line %d, splice line %d', $hRem->{lineid}, $hIns->{lineid} );
			$undos->{ $hRem->{lineid} } = 1;
			$hInc->{applied}            = 1;
			$hIns->{spliceme}           = 1;
			return 1;
		} ## end if ( $all_same > 0 )
	} ## end if ( ( $hIns->{hunkid}...))

	# c) Move somewhere else, or change include type. Can't be anything else here.
	# ---------------------------------------------------------------------------------------------
	if ( $hInc->{elogind}{hunkid} > -1 ) {

		# Just undo the removal of the elogind insert.
		my $hId = $hInc->{elogind}{hunkid};
		my $lId = $hInc->{elogind}{lineid};
		substr $hFile{hunks}[$hId]{lines}[$lId], 0, 1, $SPACE;
	} elsif ( $hIns->{elogind} ) {

		# Do not move masked includes under our block.
		$undos->{ $hRem->{lineid} } = 1;
		$hIns->{spliceme} = 1;
	} ## end elsif ( $hIns->{elogind} )

	$hInc->{applied} = 1;

	return 1;
} ## end sub include_handle_removal

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any insertion end ---
# --------------------------------------------------------------
sub is_insert_end {
	my ($line) = @_;

	( defined $line ) and ( length $line ) or return 0;

	if (       ( $line =~ m/^[${DASH}${SPACE}]?[${HASH}]endif\s*[${SLASH}](?:[${STAR}${SLASH}]+)\s*1/msx )
		|| ( $line =~ m/[${SLASH}]{2}\s+1\s+[${DASH}]{2}>\s*$/msx )
		|| ( $line =~ m/[${STAR}]\s+[${SLASH}]{2}\s+1\s+[${STAR}]{2}[${SLASH}]\s*$/msx ) )
	{
		return 1;
	} ## end if ( ( $line =~ m/^[${DASH}${SPACE}]?[${HASH}]endif\s*[${SLASH}](?:[${STAR}${SLASH}]+)\s*1/msx...))

	return 0;
} ## end sub is_insert_end

# ----------------------------------------------------------------
# --- Return 1 if the argument consists of any insertion start ---
# ----------------------------------------------------------------
sub is_insert_start {
	my ($line) = @_;

	( defined $line ) and ( length $line ) or return 0;

	if (       ( $line =~ m/^[${DASH}${SPACE}]?[${HASH}]if\s+1.+elogind/msx )
		|| ( $line =~ m/<![${DASH}]{2}\s+1.+elogind.+[${DASH}]{2}>\s*$/msx ) )
	{
		return 1;
	}

	return 0;
} ## end sub is_insert_start

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any mask else     ---
# --------------------------------------------------------------
sub is_mask_else {
	my ($line) = @_;

	( defined $line ) and ( length $line ) or return 0;

	if (       ( $line =~ m/^[${DASH}${SPACE}]?[${HASH}]else\s+[${SLASH}]+\s+0/msx )
		|| ( $line =~ m/else\s+[${SLASH}]+\s+0\s+[${DASH}]{2}>\s*$/msx )
		|| ( $line =~ m/[${STAR}]\s+else\s+[${SLASH}]+\s+0\s+[${STAR}]{2}[${SLASH}]\s*$/msx ) )
	{
		return 1;
	} ## end if ( ( $line =~ m/^[${DASH}${SPACE}]?[${HASH}]else\s+[${SLASH}]+\s+0/msx...))

	return 0;
} ## end sub is_mask_else

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any mask end      ---
# --------------------------------------------------------------
sub is_mask_end {
	my ($line) = @_;

	( defined $line ) and ( length $line ) or return 0;

	if (       ( $line =~ m/^[${DASH}${SPACE}]?[${HASH}]endif\s+[${SLASH}]+\s+0/msx )
		|| ( $line =~ m/[${SLASH}]{2}\s+0\s+[${DASH}]{2}>\s*$/msx )
		|| ( $line =~ m/[${SLASH}][${STAR}]+\s+0\s+[${STAR}]+[${SLASH}]\s*$/msx ) )
	{
		return 1;
	} ## end if ( ( $line =~ m/^[${DASH}${SPACE}]?[${HASH}]endif\s+[${SLASH}]+\s+0/msx...))

	return 0;
} ## end sub is_mask_end

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any mask start    ---
# --------------------------------------------------------------
sub is_mask_start {
	my ($line) = @_;

	( defined $line ) and ( length $line ) or return 0;

	if (
		( $line =~ m/^[${DASH}${SPACE}]?[${HASH}]if\s+0.+elogind/msx )
		|| ( ( $line =~ m/<![${DASH}]{2}\s+0.+elogind/msx )
			&& !( $line =~ m/[${DASH}]{2}>\s*$/msx ) )
		|| ( ( $line =~ m/[${SLASH}][${STAR}]{2}\s+0.+elogind/msx )
			&& !( $line =~ m/[${STAR}]{2}[${SLASH}]\s*$/msx ) )
	   )
	{
		return 1;
	} ## end if ( ( $line =~ m/^[${DASH}${SPACE}]?[${HASH}]if\s+0.+elogind/msx...))

	return 0;
} ## end sub is_mask_start

sub is_systemd_only {
	my ($text)          = @_;
	my $systemd_daemon  = q{home|import|journal|network|oom|passwor|udev};
	my $systemd_keyword = q{NR_[\{]|devel[/]};
	my $systemd_product = q{analyze|creds|cryptsetup|export|firstboot|fsck|home|import-fs|nspawn|repart|syscfg|sysusers|tmpfiles|vmspawn};

	( $text =~ m/systemd[-_]($systemd_daemon)d/msx ) and log_debug( '  => non-elogind %s', 'systemd daemon' )  and return 1;
	( $text =~ m/systemd[-_]($systemd_keyword)/msx ) and log_debug( '  => non-elogind %s', 'systemd keyword' ) and return 1;
	( $text =~ m/systemd[-_]($systemd_product)/msx ) and log_debug( '  => non-elogind %s', 'systemd product' ) and return 1;

	return 0;
} ## end sub is_systemd_only

sub logMsg {
	my ( $lvl, $fmt, @args ) = @_;

	( defined $lvl ) or $lvl = 2;

	( $LOG_DEBUG == $lvl ) and ( 0 == $do_debug ) and return 1;

	if ( !( defined $fmt ) ) {
		$fmt = shift @args // $EMPTY;
	}

	# If $fmt is now a fixed string, and @args is empty, we have to make sure that all
	# possible formatting strings are ignored, as the string might come from an error
	# handler.
	if ( 0 == scalar @args ) {
		@args = ($fmt); ## Make the fixed string the first (and only) argument
		$fmt = '%s'; ## And print it "as-is".
	}

	my $stTime  = get_time_now();
	my $stLevel = get_log_level($lvl);
	my $stMsg   = sprintf "%s|%s|%s|$fmt", $stTime, $stLevel, get_location($LOG_DEBUG), @args;

	( 0 < ( length $logfile ) ) and write_to_log($stMsg);
	( $LOG_INFO < $lvl ) and write_to_console($stMsg);

	return 1;
} ## end sub logMsg

sub log_info {
	my ( $fmt, @args ) = @_;
	return logMsg( $LOG_INFO, $fmt, @args );
}

sub log_warning {
	my ( $fmt, @args ) = @_;
	return logMsg( $LOG_WARNING, $fmt, @args );
}

sub log_error {
	my ( $fmt, @args ) = @_;
	$ret_global = 1;
	return logMsg( $LOG_ERROR, $fmt, @args );
}

sub log_status {
	my ( $fmt, @args ) = @_;
	return logMsg( $LOG_STATUS, $fmt, @args );
}

sub log_debug {
	my ( $fmt, @args ) = @_;
	$do_debug or return 1;
	return logMsg( $LOG_DEBUG, $fmt, @args );
}

sub log_change {
	my ( $txt, $change, $is_partner ) = @_;
	$do_debug or return 1;
	logMsg( $LOG_DEBUG, '%s', ${txt} );
	( defined $change ) or return logMsg( $LOG_DEBUG, ' ==> No Partner Found <==' );

	( $is_partner == 0 ) and logMsg( $LOG_DEBUG, ' -------->' );
	logMsg(
		$LOG_DEBUG,
		'        Line: %d (%s)',
		$change->{'line'} + 1,
		$change->{'done'} == $TRUE ? 'DONE' : $change->{'done'} == $FALSE ? 'Not handled, yet' : 'UNKNOWN STATE !!!'
	      );
	logMsg( $LOG_DEBUG, '        Text: %s', ( substr $change->{'text'}, 0, 77 ) . '...' );
	logMsg(
		$LOG_DEBUG,
		'        Type: %s / %s',
		$change->{'type'} == $TYPE_ADDITION ? 'Addition' : $change->{'type'} == $TYPE_REMOVAL ? 'Removal' : 'NEUTRAL !!!',
		$change->{'elogind'}                ? 'elogind'  : $change->{systemd}                 ? 'systemd' : 'UNKNOWN !!!'
	      );
	logMsg( $LOG_DEBUG, ' inside Mask: %s / in Comment: %s', $change->{'masked'} ? 'Yes' : 'No', $change->{'iscomment'} ? 'Yes' : 'No' );
	( $change->{'spliceme'} > 0 ) and logMsg( $LOG_DEBUG, '      Splice: %d', $change->{'spliceme'} );
	( $is_partner > 0 ) and logMsg( $LOG_DEBUG, ' <--------' );

	return 1;
} ## end sub log_change

sub make_location_fmt {
	my ( $lineno, $name_len ) = @_;
	my $len    = $name_len + ( ( $lineno > -1 ) ? 0 : 5 );
	my $fmtfmt = ( $lineno > -1 ) ? '%%4d:%%-%ds' : '%%-%ds';

	return sprintf $fmtfmt, $len;
} ## end sub make_location_fmt

## @brief Handles the end of an insert block by processing line markers and updating flags.
#
#  This subroutine checks if the current line marks the end of an insert block,
#  logs the current state, updates the relevant block status flags, modifies the
#  line content to remove a leading character, and sets the start and end line
#  indicators for the block. It returns success or failure based on the validity
#  of the operation.
#
#  @param $cur_idx Current index in the file being processed.
#  @param $line_p Reference to the current line being examined.
#  @param $block_start_p Reference to the starting line of the insert block.
#  @param $end_line_p Reference to where the end line should be stored.
#  @return Returns 1 if processing is successful, otherwise returns 0 or calls hunk_failed.
sub masks_handle_insert_end {
	my ( $cur_idx_p, $line_p, $block_start_p, $end_line_p ) = @_;

	if ( is_insert_end( ${$line_p} ) ) {
		log_debug( ' => Insert End  : in_mask: %d ; in_else: %d ; in_insert: %d', $in_mask_block, $in_else_block, $in_insert_block );
		$in_insert_block or return hunk_failed('check_masks: #endif // 1 found outside any insert block');

		substr ${$line_p}, 0, 1, $SPACE; ## Remove '-'
		$in_insert_block = 0;
		${$block_start_p} = -1;
		${$end_line_p}    = ${$cur_idx_p};
		${$cur_idx_p}++;

		return 1;
	} ## end if ( is_insert_end( ${...}))

	return 0;
} ## end sub masks_handle_insert_end

## @brief Handles the insertion start of a mask by checking conditions and modifying line data accordingly.
#
#  This subroutine processes a line to determine if it represents an insert start. If so, it performs
#  various checks and modifications:
#   - Logs debug information about current block states
#   - Verifies that an insert isn't already within a mask or insert block
#   - Modifies the line by replacing the first character with a space (removing '-')
#   - Updates internal state variables to indicate the start of an insert block and end of a mask block
#   - Optionally checks and modifies the previous line to ensure it has a space at the beginning
#
#  @param $cur_idx The current index in the hunk lines array.
#  @param $line reference to the current line being processed.
#  @param $block_start_p Reference to a variable indicating the block start line.
#  @param $end_line_p Reference to a variable indicating the end line of a block.
#  @param $move_to_line_p Reference to a variable indicating where to move to in the hunk lines array.
#  @return Returns 1 if the line is processed as an insert start, otherwise returns 0. Also returns
#          error codes via the hunk_failed function when certain conditions are not met.
sub masks_handle_insert_start {
	my ( $cur_idx_p, $line_p, $block_start_p, $end_line_p, $move_to_line_p ) = @_;
	my $idx = ${$cur_idx_p};

	if ( is_insert_start( ${$line_p} ) ) {
		log_debug( ' => Insert Start: in_mask: %d ; in_else: %d ; in_insert: %d', $in_mask_block, $in_else_block, $in_insert_block );
		$in_mask_block   and return hunk_failed('check_masks: Insert start found while being in a mask block!');
		$in_insert_block and return hunk_failed('check_masks: Insert start found while being in an insert block!');
		substr ${$line_p}, 0, 1, $SPACE; ## Remove '-'
		$in_insert_block = 1;
		$in_mask_block   = 0;
		${$block_start_p}  = -1;
		${$end_line_p}     = -1;
		${$move_to_line_p} = $idx;

		# While we are here we can check the previous line.
		# All inserts shall be preceded by an empty line to enhance readability.
		# So any attempt to remove them must be stopped.
		( $idx > 0 )
		        and ( $hHunk->{lines}[ $idx - 1 ] =~ m/^[${DASH}]\s*$/msx )
		        and substr $hHunk->{lines}[ $idx - 1 ], 0, 1, $SPACE;

		${$cur_idx_p}++;
		return 1;
	} ## end if ( is_insert_start( ...))
	return 0;
} ## end sub masks_handle_insert_start

## @brief Handles mask else statements by modifying line content and setting flags.
#
#  This subroutine processes "else" lines within mask blocks. If an "else"
#  is detected, it removes the leading '-' character, sets appropriate flags,
#  and moves to a new line index. The function returns 1 on success or
#  triggers an error if used outside a mask block.
#
#  @param $cur_idx Current index in the file being processed.
#  @param $line_p Reference to the current line string.
#  @param $move_to_line_p Reference to where the next processing line should be moved.
#  @return Returns 1 if an else was found and handled, 0 otherwise. Calls hunk_failed
#          with an error message if misused outside a mask block.
sub masks_handle_mask_else {
	my ( $cur_idx_p, $line_p, $move_to_line_p ) = @_;

	if ( is_mask_else( ${$line_p} ) ) {
		log_debug( ' => Mask   Else : in_mask: %d ; in_else: %d ; in_insert: %d', $in_mask_block, $in_else_block, $in_insert_block );
		$in_mask_block or return hunk_failed('check_masks: Mask else found outside any mask block!');

		substr ${$line_p}, 0, 1, $SPACE; ## Remove '-'
		$in_else_block = 1;
		${$move_to_line_p} = ${$cur_idx_p};
		${$cur_idx_p}++;

		return 1;
	} ## end if ( is_mask_else( ${$line_p...}))

	return 0;
} ## end sub masks_handle_mask_else

## @brief Handles mask end detection and processing for code blocks.
#
#  This subroutine checks if the current line marks the end of a mask block,
#  and processes it accordingly. If the line is identified as the end of a mask,
#  it logs debug information, updates state variables, modifies the line to
#  replace the initial '-' with a space, sets the block start to -1 and the end line
#  to the current index, and returns 1. Otherwise, it returns 0.
#
#  The purpose of this subroutine is to ensure proper tracking and handling of masked code blocks,
#  which helps in conditional compilation or code generation processes where specific blocks need to be masked out or inserted conditionally.
#
#  @param cur_idx The current index in the file being processed.
#  @param line_p Reference to a scalar containing the current line.
#  @param block_start_p Reference to a scalar indicating the start of the mask block.
#  @param end_line_p Reference to a scalar where the ending line number will be stored if it's an end mask.
#  @return Returns 1 if the line is processed as a mask end, otherwise returns 0.
sub masks_handle_mask_end {
	my ( $cur_idx_p, $line_p, $block_start_p, $end_line_p ) = @_;

	if ( is_mask_end( ${$line_p} ) ) {
		log_debug( ' => Mask   End  : in_mask: %d ; in_else: %d ; in_insert: %d', $in_mask_block, $in_else_block, $in_insert_block );
		$in_mask_block or return hunk_failed('check_masks: #endif // 0 found outside any mask block');

		substr ${$line_p}, 0, 1, $SPACE; ## Remove '-'
		$in_mask_block = 0;
		$in_else_block = 0;
		${$block_start_p} = -1;
		${$end_line_p}    = ${$cur_idx_p};
		${$cur_idx_p}++;

		return 1;
	} ## end if ( is_mask_end( ${$line_p...}))

	return 0;
} ## end sub masks_handle_mask_end

## @brief This subroutine handles mask start patterns in a given line within a text block.
#
#  The function checks if the current line represents a mask start and processes it accordingly.
#  If a mask start is found, it updates various flags that track the state of the text block
#  (e.g., whether the block is currently inside a mask or insert block).
#  It also ensures proper formatting by verifying that mask starts are preceded by an empty line.
#
#  @param $cur_idx The current index in the list of lines being processed.
#  @param $line_p Reference to the current line string being checked.
#  @param $block_start_p Reference to a scalar where the start index of the block will be stored.
#  @param $end_line_p Reference to a scalar where the end index of the block will be stored.
#  @param $move_to_line_p Reference to a scalar indicating whether to move to a specific line.
#  @return Returns 1 if the line is successfully processed as a mask start, otherwise returns 0.
sub masks_handle_mask_start {
	my ( $cur_idx_p, $line_p, $block_start_p, $end_line_p, $move_to_line_p ) = @_;
	my $idx = ${$cur_idx_p};

	if ( is_mask_start( ${$line_p} ) ) {
		log_debug( ' => Mask   Start: in_mask: %d ; in_else: %d ; in_insert: %d', $in_mask_block, $in_else_block, $in_insert_block );
		$in_mask_block   and return hunk_failed('check_masks: Mask start found while being in a mask block!');
		$in_insert_block and return hunk_failed('check_masks: Mask start found while being in an insert block!');
		substr ${$line_p}, 0, 1, $SPACE; ## Remove '-'
		$in_insert_block = 0;
		$in_mask_block   = 1;
		${$block_start_p}  = $idx;
		${$end_line_p}     = -1;
		${$move_to_line_p} = -1;

		# While we are here we can check the previous line.
		# All masks shall be preceded by an empty line to enhance readability.
		# So any attempt to remove them must be stopped.
		( $idx > 0 )
		        and ( $hHunk->{lines}[ $idx - 1 ] =~ m/^[${DASH}]\s*$/msx )
		        and substr $hHunk->{lines}[ $idx - 1 ], 0, 1, $SPACE;

		${$cur_idx_p}++;
		return 1;
	} ## end if ( is_mask_start( ${...}))

	return 0;
} ## end sub masks_handle_mask_start

## @brief This subroutine handles special cases when diff operations want to change or add content at the end of mask blocks.
#
#  This function specifically deals with scenarios where a diff operation adds lines immediately after exiting a mask block.
#  When this happens, those added lines need to be moved up in the sequence. The function adjusts the order of lines
#  within the current hunk to handle these cases correctly. It modifies the $hHunk structure by moving lines around while
#  maintaining proper ordering. This is necessary because our block-based approach means diff operations could alter
#  line positions unexpectedly.
#
#  @param cur_idx The current index in the hunk's lines array.
#  @param line_p Reference to a scalar containing the current line being processed.
#  @param end_line_p Reference to a scalar indicating the ending line of processing.
#  @param move_to_line_p Reference to a scalar that determines where to move the current line to.
#  @return Returns 1 if lines were moved successfully, otherwise returns 0.
sub masks_sanitize_additions {
	my ( $cur_idx, $line_p, $end_line_p, $move_to_line_p ) = @_;

	# A special thing to consider is when diff wants to change the end or
	# add something to the end of a mask block, or right before an insertion
	# block.
	# As our blocks are getting removed by diff, the addition will happen
	# right after that. So anything added the very next lines after we have
	# exited our domain must be moved up.
	if ( 0 == $in_mask_block ) {
		if ( ( ${$move_to_line_p} > -1 ) && ( ${$line_p} =~ m/^[${PLUS}]/msx ) ) {
			my $cpy_line = ${$line_p};
			( splice @{ $hHunk->{lines} }, $cur_idx, 1 ); ## Order matters here.
			( splice @{ $hHunk->{lines} }, ${$move_to_line_p}++, 0, $cpy_line );

			# Note: Again no change to $hHunk->{count} here, as the lines are moved.
			return 1;
		} ## end if ( ( ${$move_to_line_p...}))

		# end our mask block ending awareness at the first non-insertion line after a mask block.
		# ---------------------------------------------------------------------------------------
		${$end_line_p}     = -1;
		${$move_to_line_p} = -1;
	} ## end if ( 0 == $in_mask_block)

	return 0;
} ## end sub masks_sanitize_additions

## @brief Subroutine to sanitize specific blocks for elogind compatibility by adjusting line prefixes and handling special cases.
#
#  This subroutine masks_sanitize_elogind_blocks is used to process lines within insert and mask-else blocks,
#  removing specific prefixes ('-' or ' ') and handling certain edge cases that could cause issues during patching.
#  The function checks for lines with a leading '-' prefix, replacing them with spaces. Additionally, it handles
#  special scenarios where lines need to be copied or moved above else/insert points to maintain proper order
#  within the hunk of lines being processed. This ensures that masking and insertion operations work correctly.
#
#  @param $cur_idx_p Reference to current index in the line array (scalar reference).
#  @param $line_p Reference to the current line being processed (scalar reference).
#  @param $block_start_p Reference to the start of the block (scalar reference).
#  @param $end_line_p Reference to the end line of the block (scalar reference).
#  @param $move_to_line_p Reference to the line number where moves should be made (scalar reference).
#  @return Returns 1 if a modification was made, otherwise returns 0.
sub masks_sanitize_elogind_blocks {
	my ( $cur_idx_p, $line_p, $block_start_p, $end_line_p, $move_to_line_p ) = @_;

	if ( $in_insert_block || ( $in_mask_block && $in_else_block ) ) {

		# Remove '-' prefixes in all lines within insert and mask-else blocks
		# -------------------------------------------------------------------
		if ( ${$line_p} =~ m/^[${DASH}]/msx ) {
			substr ${$line_p}, 0, 1, $SPACE; ## Remove '-'
			${$cur_idx_p}++;

			return 1;
		} ## end if ( ${$line_p} =~ m/^[${DASH}]/msx)

		# Special check for additions/keepers that might (will!) wreak havoc:
		# -------------------------------------------------------------------
		if ( ${$move_to_line_p} > -1 ) {

			# The following cases have been met:
			# a) upstream adds something after a mask #else block ( See issues #1 and #4 )
			# b) name reverts push lines under a mask start
			# c) diff removes lines from a masked block or before an insert, but keeps
			#    common lines inside mask-else or insert blocks
			# d) as a follow-up on c), diff wants to add a line and adds it after the
			#    kept common line inside our domain.
			# All these cases can be handled with two simple solutions.
			# ------------------------------------------------------------------------------------
			my $cpy_line = ${$line_p};

			# Case 1 ; The keeper: Copy the offending line back above the else/insert
			# -----------------------------------------------------------------------
			if ( ${$line_p} =~ m/^[${SPACE}]/msx ) {
				substr $cpy_line, 0, 1, "${PLUS}"; ## Above, this is an addition.
				( splice @{ $hHunk->{lines} }, ${$move_to_line_p}++, 0, $cpy_line );
				$hHunk->{count} += 1;
				${$cur_idx_p}++; ## We have to advance i, or the next iteration puts as back here.
			} ## end if ( ${$line_p} =~ m/^[${SPACE}]/msx)

			# Case 2 ; The addition: move the offending line back above the else/insert
			# -----------------------------------------------------------------------
			else {
				( splice @{ $hHunk->{lines} }, ${$cur_idx_p}, 1 ); ## Order matters here.
				( splice @{ $hHunk->{lines} }, ${$move_to_line_p}++, 0, $cpy_line );

				# Note: No change to $hHunk->{count} here, as the lines are moved.
			} ## end else [ if ( ${$line_p} =~ m/^[${SPACE}]/msx)]

			# No matter whether we have copied or moved, the if/else moved down.
			${$end_line_p} > -1 and ++${$end_line_p} or ++${$block_start_p};

			${$cur_idx_p}++;
			return 1;
		} ## end if ( ${$move_to_line_p...})
	} ## end if ( $in_insert_block ...)

	return 0;
} ## end sub masks_sanitize_elogind_blocks

## @brief Prepares shell and meson files for patch processing by commenting out masked blocks.
#
#  This subroutine reads a source file and processes it to handle masked blocks
#  (typically used in C preprocessor contexts) by commenting them out. This is
#  necessary because the patch building system expects masking syntax to be
#  handled uniformly across all file types, including shell and meson files which
#  are not processed by a preprocessor. Without this step, diff may incorrectly
#  move commented sections and uncomment them in the generated patches.
#
#  @return Returns 1 on successful completion.
sub prepare_shell {
	my $in   = $hFile{source};
	my $out  = $in . '.pwx';
	my @lIn  = ();
	my @lOut = ();

	# Leech the source file
	if ( open my $fIn, '<', $in ) {
		@lIn = <$fIn>;
		close $fIn or croak("Closing '$fIn' FAILED: $!\n");
	} else {
		croak("$in can not be opened for reading! [$!]");
	}

	# -----------------------------------------------------------------------
	# --- Prepare shell and meson files for our processing.               ---
	# --- If this is a shell or meson file, we have to adapt it first:    ---
	# --- To be able to use our patch building system/ the files use the  ---
	# --- same masking technology as the C files. But as these are not    ---
	# --- handled by any preprocessor/ it is necessary to comment out all ---
	# --- masked blocks.                                                  ---
	# --- If we do not do this, diff creates patches which move all       ---
	# --- commented blocks behind the #endif and uncomment them.          ---
	# -----------------------------------------------------------------------

	# Now prepare the output, line by line.
	my $is_block = 0;
	my $is_else  = 0;
	my $line_no  = 0;
	for my $line (@lIn) {

		chomp $line;
		++$line_no;

		if ( is_mask_start($line) ) {
			if ( $is_block > 0 ) {
				log_error( '%s:%d : Mask start in mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 1;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_start($line...))

		if ( is_mask_else($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask else outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_else = 1;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_else($line...))

		if ( is_mask_end($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask end outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 0;
			$is_else  = 0;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_end($line...))

		if ( $is_block && !$is_else ) {
			$line =~ s/^[${HASH}]\s?//msgx;
			$line =~ s/^\s\s[${STAR}]\s?//msgx;
		}

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open my $fOut, '>', $out ) {
		for my $line (@lOut) {
			print {$fOut} "$line\n";
		}
		close $fOut or croak("Closing '$fOut' FAILED: $!\n");
	} else {
		croak("$out can not be opened for writing! [$!]");
	}

	# The temporary file is our new source
	$hFile{source} = $out;

	return 1;
} ## end sub prepare_shell

## @brief Prepares an XML file for processing by handling mask blocks and correcting double dash entities.
#
#  This function reads an input XML file and processes it to handle special mask blocks denoted by
#  specific start, else, and end markers. During this process, it also converts &#x2D; entities
#  back to regular dashes within masked sections to ensure proper XML parsing. The processed output
#  is written to a temporary file with a ".pwx" extension.
#
#  @return Returns 1 on successful processing.
sub prepare_xml {
	my $in   = $hFile{source};
	my $out  = $in . '.pwx';
	my @lIn  = ();
	my @lOut = ();

	# Leech the source file
	if ( open my $fIn, '<', $in ) {
		@lIn = <$fIn>;
		close $fIn or croak("Closing '$fIn' FAILED: $!\n");
	} else {
		croak("$in can not be opened for reading! [$!]");
	}

	# -----------------------------------------------------------------------
	# --- The masking of unneeded blocks in XML files is done using a     ---
	# --- comment scheme. Unfortunately the standard forbids double dashes---
	# --- in comments. To be able to process XML files nevertheless, they ---
	# --- are updated by unprepare_xml() so that all double dashes in     ---
	# --- comments are substituted by &#x2D;&#x2D;, which must be reversed---
	# --- here or the further processing would go nuts.                   ---
	# -----------------------------------------------------------------------

	# Now prepare the output, line by line.
	my $is_block = 0;
	my $is_else  = 0;
	my $line_no  = 0;
	for my $line (@lIn) {

		chomp $line;
		++$line_no;

		if ( is_mask_start($line) ) {
			if ( $is_block > 0 ) {
				log_error( '%s:%d : Mask start in mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 1;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_start($line...))

		if ( is_mask_else($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask else outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_else = 1;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_else($line...))

		if ( is_mask_end($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask end outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 0;
			$is_else  = 0;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_end($line...))

		if ( $is_block && !$is_else ) {
			$line =~ s/&#x2D;/-/msg;
		}

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open my $fOut, '>', $out ) {
		for my $line (@lOut) {
			print {$fOut} "$line\n";
		}
		close $fOut or croak("Closing '$fOut' FAILED: $!\n");
	} else {
		croak("$out can not be opened for writing! [$!]");
	}

	# The temporary file is our new source
	$hFile{source} = $out;

	return 1;
} ## end sub prepare_xml

## @brief Protects configuration lines from unwanted changes during patch application.
#
#  This subroutine processes a hunk of configuration lines to prevent addition of
#  unnecessary lines and handles special cases for elogind's [Sleep] block. It removes
#  lines that match specific patterns related to NAutoVTs or ReserveVT, and manages
#  the deletion of lines within the [Sleep] block by converting deletions to additions.
#
#  @return Returns 1 on successful processing.
sub protect_config() {

	# early exits:
	( defined $hHunk ) or croak('check_masks: hHunk is undef');
	$hHunk->{useful}   or croak('check_masks: Nothing done but hHunk is useless?');

	my $is_sleep_block = 0;
	my $cur_idx        = 0;
	while ( $cur_idx < $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[ $cur_idx++ ]; ## Shortcut

		# Kill addition of lines we do not need
		# ---------------------------------------
		if ( ${$line} =~ m/^[${PLUS}][${HASH}]?(?:NAutoVTs|ReserveVT)/msx ) {
			splice @{ $hHunk->{lines} }, $cur_idx--, 1;
			--$hHunk->{count};
			next;
		}

		# enter elogind specific [Sleep] block
		# ------------------------------------------
		if ( ${$line} =~ m/^[${DASH}]\[Sleep\]/msx ) {
			substr ${$line}, 0, 1, $SPACE; ## Remove '-'

			# The previous line is probably the deletion of the blank line before the block
			( $cur_idx > 0 ) and ( $hHunk->{lines}[ $cur_idx - 1 ] =~ /^[${DASH}]/ms ) and $hHunk->{lines}[ $cur_idx - 1 ] = $SPACE;

			$is_sleep_block = 1;
			next;
		} ## end if ( ${$line} =~ m/^[${DASH}]\[Sleep\]/msx)

		# Remove deletions of lines in our [Sleep] block
		$is_sleep_block
		        and ( ${$line} =~ m/^[${DASH}]/ms )
		        and ( substr ${$line}, 0, 1, $SPACE ) ## Remove '-'
		        and next;

		# No sleep block
		$is_sleep_block = 0;

	} ## end while ( $cur_idx < $hHunk...)

	return hunk_is_useful();
} ## end sub protect_config

## @brief Prunes leading and trailing lines from a hunk if they are not useful.
#
#  This function examines the lines within a hunk to determine if leading or
#  trailing lines can be removed without losing important context. It specifically
#  tracks masked regions and adjusts the hunk's start position and line count
#  accordingly. The pruning is limited to at most three lines from each end.
#
#  @return Returns 1 on successful pruning, or 0 if the hunk is not defined or not useful.
sub prune_hunk() {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Pruning Hunk ...');

	# Go through the lines and see what we've got.
	my @mask_info = ( $hHunk->{masked_start} );
	my $prefix    = 0;
	my $postfix   = 0;
	my $changed   = 0; ## Set to 1 once the first change was found.

	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = $hHunk->{lines}[$i]; ## Shortcut
		if ( $line =~ m/^[${DASH}${PLUS}]/msx ) {
			$changed = 1;
			$postfix = 0;
		} else {
			$changed or ++$prefix;
			++$postfix;
		}

		# We have to note down mask changes, that might get pruned.
		# If any is found, the hunks masked_start must be set to it.
		if ( 0 == $changed ) {
			$mask_info[ $i + 1 ] =
			          is_mask_end($line)   ? -1
			        : is_mask_else($line)  ? -1
			        : is_mask_start($line) ? 1
			        :                        0;
		} ## end if ( 0 == $changed )

		# Note: The last action still stands, no matter whether it gets pruned
		#       or not, as it is only relevant for the next hunk.
	} ## end for my $i ( 0 .. $hHunk...)

	# Now let's prune it:
	if ( $prefix > 3 ) {
		$prefix -= 3;
		log_debug( '  => Splicing first %d lines', $prefix );
		splice @{ $hHunk->{lines} }, 0, $prefix;
		$hHunk->{src_start} += $prefix;
		$hHunk->{count}     -= $prefix;

		# If any mask state change gets pruned, we have to remember the last one:
		for my $i ( $prefix .. 0 ) {
			if ( $mask_info[$i] ) {
				$hHunk->{masked_start} = $mask_info[$i] > 0 ? 1 : 0;
				last;
			}
		} ## end for my $i ( $prefix .. ...)
	} ## end if ( $prefix > 3 )
	if ( $postfix > 3 ) {
		$postfix -= 3;
		log_debug( '  => Splicing last %d lines', $postfix );
		splice @{ $hHunk->{lines} }, $hHunk->{count} - $postfix, $postfix;
		$hHunk->{count} -= $postfix;
	} ## end if ( $postfix > 3 )

	return 1;
} ## end sub prune_hunk

## @brief Unprepares shell and meson files after processing by commenting out content between elogind markers.
#
#  This function reverses the actions performed by prepare_shell() by uncommenting
#  lines that were previously commented out between elogind-specific mask start/end markers.
#  It handles both temporary .pwx files and the final output patch generation.
#  The function ensures proper handling of nested blocks and validates marker usage.
#
#  @return Returns 1 on successful unpreparation, croaks on file operation errors or illegal marker usage.
sub unprepare_shell {
	my $in   = $hFile{source};
	my $out  = substr $in, 0, -4;
	my @lIn  = ();
	my @lOut = ();

	# Do not handle XML files here
	$hFile{is_xml} and return 0;

	# Leech the temporary file
	if ( open my $fIn, '<', $in ) {
		@lIn = <$fIn>;
		close $fIn or croak("Closing '$fIn' FAILED: $!\n");
	} else {
		croak("$in can not be opened for reading! [$!]");
	}

	# -----------------------------------------------------------------------
	# --- Unprepare shell (and meson) files after our processing          ---
	# --- In prepare_shell() we have commented in all content between our ---
	# --- elogind markers, to help diff not to juggle our blocks around.  ---
	# --- Now these blocks must be commented out again.                   ---
	# --- We have an advantage and a disadvantage here. On one hand, we   ---
	# --- can do the changes within $hFile{output}, as that is the final  ---
	# --- patch. On the other hand, we do not know whether really all     ---
	# --- lines in the source where commented out. The latter means, that ---
	# --- if we blindly comment out all block lines, the resulting patch  ---
	# --- may fail. We therefore write the temporary .pwx file back, and  ---
	# --- and ensure that all lines are commented out.                    ---
	# -----------------------------------------------------------------------

	# Now prepare the output, line by line.
	my $is_block = 0;
	my $is_else  = 0;
	my $line_no  = 0;
	for my $line (@lIn) {

		chomp $line;
		++$line_no;

		if ( is_mask_start($line) ) {
			if ( $is_block > 0 ) {
				log_error( '%s:%d : Mask start in mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 1;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_start($line...))

		if ( is_mask_else($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask else outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_else = 1;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_else($line...))

		if ( is_mask_end($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask end outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 0;
			$is_else  = 0;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_end($line...))

		if (       $is_block
			&& !$is_else
			&& ( '# #' ne ( substr $line, 0, 3 ) )
			&& ( '  * ' ne ( substr $line, 0, 4 ) ) )
		{
			$hFile{source} =~ m/${DOT}sym${DOT}pwx$/msx and $line = '  * ' . $line
			        or $line = '# ' . $line;

			# Do not create empty comment lines with trailing spaces.
			$line =~ s/([${HASH}])\s+$/$1/msgx;
		} ## end if ( $is_block && !$is_else...)

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open my $fOut, '>', $out ) {
		for my $line (@lOut) {
			print {$fOut} "$line\n";
		}
		close $fOut or croak("Closing '$fOut' FAILED: $!\n");
	} else {
		croak("$out can not be opened for writing! [$!]");
	}

	# Remove the temporary file
	unlink $in or croak("Unlinking $in FAILED: $!\n");

	# Now prepare the patch. It is like above, but with less checks.
	# We have to move out the lines first, and then write them back.
	$is_block = 0;
	$is_else  = 0;
	@lIn      = splice @{ $hFile{output} };

	for my $line (@lIn) {
		if ( $line =~ m/[${HASH}]\s+masked_(?:start|end)\s+([01])$/msx ) {
			$1        and $is_block = 1 or $is_block = 0;
			$is_block and $is_else  = 0; ## can't be.
			next; ## do not transport this line
		}
		is_mask_end($line)   and $is_block = 0;
		is_mask_start($line) and $is_block = 1;
		$is_block or $is_else = 0;
		is_mask_else($line) and $is_else = 1;
		$is_block
		        and ( !$is_else )
		        and $ATAT ne ( substr $line, 0, 2 )
		        and ( !( $line =~ m/^[-${SPACE}]+[${HASH}](?:if|else|endif)/msx ) )
		        and ( substr $line, 1, 0, "${HASH}${SPACE}" );

		# Make sure not to demand to add empty comment lines with trailing spaces
		$line =~ s/^([${PLUS}][${HASH}])\s+$/$1/msgx;
		push @{ $hFile{output} }, $line;
	} ## end for my $line (@lIn)

	# Now source is the written back original:
	$hFile{source} = $out;

	return 1;
} ## end sub unprepare_shell

## @brief Unprepares an XML file by masking double dashes in mask blocks and handling patch preparation.
#
#  This function processes a temporary source file, masking all occurrences of '--' within
#  mask blocks to prevent issues with XML comment parsing. It also prepares the output for
#  patching by removing mask-related lines and applying the same masking logic to the
#  final output buffer.
#
#  @return Returns 1 on successful processing, croaks on file access errors or illegal file structures.
sub unprepare_xml {
	my $in   = $hFile{source};
	my $out  = substr $in, 0, -4;
	my @lIn  = ();
	my @lOut = ();

	# Do not handle shell files here
	$hFile{is_sh} and return 0;

	# Leech the temporary file
	if ( open my $fIn, '<', $in ) {
		@lIn = <$fIn>;
		close $fIn or croak("Closing '$fIn' FAILED: $!\n");
	} else {
		croak("$in can not be opened for reading! [$!]");
	}

	# -----------------------------------------------------------------------
	# --- Before we can allow an XML file to live, all double dashes that ---
	# --- happen to reside in one of our mask blocks must be masked.      ---
	# --- The standard forbids double dashes inside comments, so we solve ---
	# --- this by substituting '--' with '&#x2D;&#x2D;'.                  ---
	# -----------------------------------------------------------------------

	# Now prepare the output, line by line.
	my $is_block = 0;
	my $is_else  = 0;
	my $line_no  = 0;
	for my $line (@lIn) {

		chomp $line;
		++$line_no;

		if ( is_mask_start($line) ) {
			if ( $is_block > 0 ) {
				log_error( '%s:%d : Mask start in mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 1;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_start($line...))

		if ( is_mask_else($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask else outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_else = 1;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_else($line...))

		if ( is_mask_end($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask end outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 0;
			$is_else  = 0;
			push @lOut, $line;
			next;
		} ## end if ( is_mask_end($line...))

		if ( $is_block && !$is_else ) {
			$line =~ s/--/&#x2D;&#x2D;/msg;
		}

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open my $fOut, '>', $out ) {
		for my $line (@lOut) {
			print {$fOut} "$line\n";
		}
		close $fOut or croak("Closing '$fOut' FAILED: $!\n");
	} else {
		croak("$out can not be opened for writing! [$!]");
	}

	# Remove the temporary file
	unlink $in or croak("Unlinking $in FAILED: $!\n");

	# Now prepare the patch. It is like above, but with less checks.
	# We have to move out the lines first, and then write them back.
	@lIn      = ();
	$is_block = 0;
	$is_else  = 0;
	@lIn      = splice @{ $hFile{output} };
	for my $line (@lIn) {
		if ( $line =~ m/[${HASH}]\s+masked_(?:start|end)\s+([01])$/msx ) {
			$1        and $is_block = 1 or $is_block = 0;
			$is_block and $is_else  = 0; ## can't be.
			next; ## do not transport this line
		}
		is_mask_end($line)   and $is_block = 0;
		is_mask_start($line) and $is_block = 1;
		$is_block or $is_else = 0;
		is_mask_else($line) and $is_else = 1;
		$is_block
		        and ( !$is_else )
		        and $line =~ s/([^<!]+)--([^>]+)/${1}&#x2D;&#x2D;${2}/msgx;

		push @{ $hFile{output} }, $line;
	} ## end for my $line (@lIn)

	# Now source is the written back original:
	$hFile{source} = $out;

	return 1;
} ## end sub unprepare_xml

## @brief Reads and records include directives from a hunk, tracking additions, removals, and elogind-specific blocks.
#
#  This subroutine processes the lines of a hunk to identify include directives that are added or removed.
#  It tracks comments indicating removals of includes and insertions of new includes. It also identifies
#  sections of the code that are "needed by elogind" and marks those includes accordingly.
#
#  @return Returns 1 to indicate successful completion.
sub read_includes {

	# early exits:
	( defined $hHunk ) or return 0;
	$hHunk->{useful}   or return 0;

	log_debug('Reading includes ...');

	# We must know when "needed by elogind blocks" start
	my $in_elogind_block = 0;
	for my $i ( 0 .. $hHunk->{count} - 1 ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Note down removals of includes we commented out
		if ( ${$line} =~ m/^[${DASH}]\s*\/[${SLASH}${STAR}]+\s*[${HASH}]include\s+([<"'])([^>"']+)([>"'])/msx ) {
			( defined $hIncs{$2}{remove} )
			        and log_debug( 'Line % 3d Include %s removal first in line %d', $i + 1, $2, $hIncs{$2}{remove}{lineid} + 1 )
			        and next;
			log_debug( 'Recording remove commented at % 3d: %s%s%s', $i + 1, $1, $2, $3 );
			$hIncs{$2}{remove} = {
				elogind  => $in_elogind_block,
				hunkid   => $hHunk->{idx},
				lineid   => $i,
				spliceme => 0,
				sysinc   => ( $1 eq '<' ) ? 1 : 0
			};
			next;
		} ## end if ( ${$line} =~ m/^[${DASH}]\s*\/[${SLASH}${STAR}]+\s*[${HASH}]include\s+([<"'])([^>"']+)([>"'])/msx)

		# Note down inserts of possibly new includes we might want commented out
		if ( ${$line} =~ m/^[${PLUS}]\s*[${HASH}]include\s+([<"'])([^>"']+)([>"'])/msx ) {
			( defined $hIncs{$2}{insert} )
			        and log_debug( 'Line % 3d Include %s insertion first in line %d', $i + 1, $2, $hIncs{$2}{insert}{lineid} + 1 )
			        and next;
			log_debug( 'Recording adding new       at % 3d: %s%s%s', $i + 1, $1, $2, $3 );
			$hIncs{$2}{insert} = {
				elogind  => $in_elogind_block,
				hunkid   => $hHunk->{idx},
				lineid   => $i,
				spliceme => 0,
				sysinc   => ( $1 eq '<' ) ? 1 : 0
			};
			next;
		} ## end if ( ${$line} =~ m/^[${PLUS}]\s*[${HASH}]include\s+([<"'])([^>"']+)([>"'])/msx)

		# Note down removals of includes we explicitly added for elogind
		if ( $in_elogind_block && ( ${$line} =~ m/^[${DASH}]\s*[${HASH}]include\s+([<"'])([^>"']+)([>"'])/msx ) ) {
			( defined $hIncs{$2}{elogind} )
			        and log_debug( 'Line % 3d elogind Include %s first in line %d', $i + 1, $2, $hIncs{$2}{elogind}{lineid} + 1 )
			        and next;
			log_debug( 'Recording remove elogind   at % 3d: %s%s%s', $i + 1, $1, $2, $3 );
			$hIncs{$2}{elogind} = { hunkid => $hHunk->{idx}, lineid => $i };
			next;
		} ## end if ( $in_elogind_block...)

		# elogind include blocks are started by a comment featuring "needed by elogind"
		if ( ${$line} =~ m/^[ -]\s*[${SLASH}]+.*needed\s+(?:by|for)\s+elogind.*/msxi ) {
			log_debug( 'Entering elogind include block at line %d', $i + 1 );
			$in_elogind_block = 1;
			next;
		}

		# elogind include blocks end, when the first non-include line is found
		if ( $in_elogind_block && !( ${$line} =~ m/^[${DASH}${PLUS}${SPACE}]\s*[${HASH}]include\s*/misx ) ) {
			log_debug( 'Leaving elogind include block at line %d', $i + 1 );
			$in_elogind_block = 0;
		}
	} ## end for my $i ( 0 .. $hHunk...)

	return 1;
} ## end sub read_includes

## @brief Subroutine to refactor hunks by applying various checks and conditionally pruning them
#
#  This subroutine iterates through all hunks of a file and applies specific
#  condition-based checks. If any check determines that a hunk is no longer
#  necessary, the hunk is pruned (removed). The order of checks matters as each
#  one has its own specific conditions to evaluate.
#
#  @return Returns 1 after processing all hunks in the file.
sub refactor_hunks {
	for my $pos ( 0 .. $hFile{count} - 1 ) {

		# Break off if a signal was caught
		( $death_note > 0 ) and ( $pos = $hFile{count} ) and next;

		log_debug( 'Checking Hunk %d', $pos + 1 );
		$hHunk = $hFile{hunks}[$pos]; ## Global shortcut

		# === Special 1) protect src/login/logind.conf.in =================
		if ( $hFile{source} =~ m/src\/login\/logind[${DOT}]conf[${DOT}]in/msx ) {
			protect_config() or next;
		}

		# === 1) Check for elogind masks 1 (normal source code) ===========
		check_masks() or next;

		# === 2) Check for elogind masks 2 (symbol files) =================
		check_sym_lines() or next;

		# === 3) Check for musl_libc compatibility blocks =================
		check_musl() or next;

		# === 4) Check for __STDC_VERSION guard removals ==================
		check_stdc_version() or next;

		# === 5) Check for debug constructs ===============================
		check_debug() or next;

		# === 6) Check for useful blank line additions ====================
		check_blanks() or next;

		# === 7) Check for 'elogind' => 'systemd' reverts =================
		%hProtected = ();
		check_name_reverts() or next;

		# === 8) Check for elogind_*() function removals ==================
		check_func_removes() or next;

		# === 9) Check for elogind extra comments and information =========
		check_comments() or next;

		# === 10) Check for any useless changes that do nothing ============
		check_useless() or next;

		# === 11) Check for empty masks that guard nothing any more =======
		check_empty_masks() or next;

		#  ===> IMPORTANT: From here on no more pruning, lines must *NOT* change any more! <===

		# === 11) Analyze includes and note their appearance in $hIncs =====
		read_includes(); ## Never fails, doesn't change anything.

	} ## end for my $pos ( 0 .. $hFile...)

	return 1;
} ## end sub refactor_hunks

sub set_log_file {
	my ($name) = @_;
	$logfile = sprintf '%s-%s.log', $name, get_date_now();
	return 1;
}

## @brief Displays progress information on console or logs it to file.
#
#  This subroutine outputs a progress message to either the console or a log file,
#  depending on the value of $log_as_status. It clears any previous progress line
#  before printing the new one to ensure clean output. If logging to a file, it
#  writes the message using log_status() and ensures no empty lines are added.
#
#  @param $log_as_status  If positive, logs the message to file; otherwise prints to console.
#  @param $fmt            Format string for the progress message.
#  @param @args           Arguments to be formatted into the progress message.
#  @return               Always returns 1.
sub show_progress {
	my ( $log_as_status, $fmt, @args ) = @_;
	my $progress_str = sprintf $fmt, @args;

	# Clear a previous progress line
	( $have_progress_msg > 0 ) and print "\r" . ( $SPACE x length $progress_str ) . "\r";

	if ( 0 < $log_as_status ) {

		# Write into log file
		$have_progress_msg = 0; ## ( We already deleted the line above, leaving it at 1 would add a useless empty line. )
		log_status( '%s', $progress_str );
	} else {

		# Output on console
		$have_progress_msg = 1;
		local $| = 1;
		print "\r${progress_str}";
	} ## end else [ if ( 0 < $log_as_status)]

	return 1;
} ## end sub show_progress

## @brief Signal handler to manage specific signals and prevent infinite loops.
#
#  This subroutine handles signals by tracking their occurrences. If a signal is caught more than five times,
#  it logs an error and forcefully terminates the process. Otherwise, it logs a warning and continues execution.
#  Unknown signals are ignored after logging a warning.
#
#  @return Returns 1 to indicate successful handling of the signal.
sub sigHandler {
	my ($sig) = @_;
	if ( exists $SIGS_CAUGHT{$sig} ) {
		if ( ++$death_note > 5 ) {

			# This is very crude, so only do _THAT_ if everything else failed
			log_error( undef, 'Caught %s Signal %d times - breaking all off!', $sig, $death_note );
			kill 'KILL', $$ or croak('KILL failed');
		} else {
			log_warning( undef, 'Caught %s Signal - Ending Tasks...', $sig );
		}
	} else {
		log_warning( 'Caught Unknown Signal [%s] ... ignoring Signal!', $sig );
	}
	return 1;
} ## end sub sigHandler

## @brief Splices out include additions that were marked for removal.
#
#  This subroutine processes the tracked include additions and removes them from
#  the corresponding hunks in the file. It ensures that the line IDs are valid
#  and within bounds before performing the splice operation. The splicing is done
#  in reverse order to maintain correct indices during modification.
#
#  @return Returns 1 on successful completion.
sub splice_includes {

	log_debug('Splicing undone include additions ...');

	# First build a tree of the includes to splice:
	my %incMap = ();
	for my $inc ( keys %hIncs ) {
		if ( $hIncs{$inc}{insert}{spliceme} ) {
			my $hId = $hIncs{$inc}{insert}{hunkid};
			my $lId = $hIncs{$inc}{insert}{lineid};

			# Sanity checks:
			$hId > -1 or log_warning( 'splice_includes : Inc %s has Hunk Id -1!', $inc ) and next;
			if ( -1 == $lId ) {
				$hHunk = $hFile{hunks}[$hId];
				hunk_failed("splice_includes: $inc has line id -1!");
				next;
			}
			if ( $lId >= $hFile{hunks}[$hId]{count} ) {
				$hHunk = $hFile{hunks}[$hId];
				hunk_failed("splice_includes: $inc line id $lId/$hFile{hunks}[$hId]{count}!");
				next;
			}

			# Record the include line
			$incMap{$hId}{$lId} = 1;
		} ## end if ( $hIncs{$inc}{insert...})
	} ## end for my $inc ( keys %hIncs)

	# Now we can do the splicing in an ordered way:
	for my $hId ( sort { $a <=> $b } keys %incMap ) {

		# Go through the lines in reverse, that should be save:
		for my $lId ( reverse sort { $a <=> $b } keys %{ $incMap{$hId} } ) {
			splice @{ $hFile{hunks}[$hId]{lines} }, $lId, 1;
			$hFile{hunks}[$hId]{count}--;
		}
	} ## end for my $hId ( sort { $a...})

	return 1;
} ## end sub splice_includes

sub strempty {
	my ($str) = @_;
	( defined $str ) and return $str;
	return $EMPTY;
}

sub validate_block_counters {

	# Do not allow negative values:
	$in_mask_block < 0 and $in_mask_block = 0;
	$in_else_block < 0 and $in_else_block = 0;
	return 1;
} ## end sub validate_block_counters

## @brief Callback function for File::Find to identify source files for processing.
#
#  This subroutine is used by the File::Find module to locate relevant source files
#  in the repository. It ensures that only regular files are considered, filters
#  out temporary .pwx files and generated man/rules directories, and populates the
#  @source_files array with the paths of identified files.
#
#  The function normalizes file paths by ensuring they start with './' if not already,
#  checks for relevant file properties (regular file), verifies against existing wanted
#  files or global state ($have_wanted), excludes certain patterns (.pwx and man/rules),
#  and adds the file to @source_files array if all conditions are met.
#
#  It also updates a hash reference $hWanted with status 2 for each processed file.
#
#  @return Returns 1 to continue File::Find traversal. No other values returned.
sub wanted {
	my $filepath  = $_;
	my $f         = $File::Find::name;
	my $is_wanted = 0;

	$f =~ m/^[${DOT}][${SLASH}]/msx or $f = "./$f";

	-f $filepath
	        and ( ( 0 == $have_wanted ) or ( defined $hWanted{$f} ) )
	        and ( !( $filepath         =~ m/${DOT}]pwx$/ms ) )
	        and ( !( $File::Find::name =~ m/man[${SLASH}]rules[${SLASH}]/msx ) ) ## Protect generated man rules (Issue #3)
	        and push @source_files, $File::Find::name
	        and $is_wanted = 1;

	$is_wanted and $hWanted{$f} = 2;

	return 1;
} ## end sub wanted

# A warnings handler that lets perl warnings be printed via log
sub warnHandler {
	my ($warn) = @_;
	return log_warning( '%s', $warn );
}

## @brief Writes a message to the console with progress handling.
#
#  This subroutine prints a given message to the console. If a progress message
#  has been previously printed, it adds a newline before the current message
#  to ensure proper formatting. It also enables autoflush for the output
#  stream to guarantee immediate display of the message.
#
#  @param msg The message to be printed to the console.
#  @return The return value of the print function, which is the number of
#          characters printed.
sub write_to_console {
	my ($msg) = @_;

	if ( $have_progress_msg > 0 ) {
		print "\n";
		$have_progress_msg = 0;
	}

	local $| = 1;
	return print "${msg}\n";
} ## end sub write_to_console

## @brief Appends a message to the log file.
#
#  This subroutine opens the global logfile in append mode, writes the provided
#  message followed by a newline, and then closes the file handle. It uses
#  lexical filehandle for better resource management and includes error handling
#  with confess() in case closing the file fails.
#
#  @return Returns 1 upon successful completion.
sub write_to_log {
	my ($msg) = @_;

	if ( open my $fLog, '>>', $logfile ) {
		print {$fLog} "${msg}\n";
		close $fLog or confess("Closing logfile '$logfile' FAILED!");
	}

	return 1;
} ## end sub write_to_log

## @brief This subroutine writes content to a patch file from an array reference.
#
#  The subroutine attempts to open a file handle for writing to $hFile{patch}.
#  If successful, it iterates through each line in $hFile{output}, modifies certain
#  lines if needed based on the value of $hFile{pwxfile} and regular expression matching,
#  and writes them to the output file. After processing all lines, it closes the file handle.
#  If opening or closing the file fails, appropriate error messages are logged.
#
#  The line modification is specific for shell files where trailing spaces in certain
#  comment lines should be removed without assuming they are empty.
#
#  @return Returns 1 on successful completion. In case of failure to open the output file,
#          it logs an error message, confesses a fatal error and does not return.
sub write_to_patch {
	if ( open my $fOut, '>', $hFile{patch} ) {
		for my $line ( @{ $hFile{output} } ) {

			# Do not assume empty comment lines with trailing spaces in shell files
			$hFile{pwxfile} and $line =~ s/([+ -][${HASH}])\s+$/$1/msgx;
			print {$fOut} "$line\n";
		} ## end for my $line ( @{ $hFile...})
		close $fOut or croak("Closing '$fOut' FAILED: $!\n");
	} else {
		log_error( "ERROR: %s could not be opened for writing!\n%s\n", $hFile{patch}, $! );
		confess('Please fix this first!');
	}

	return 1;
} ## end sub write_to_patch

__END__

# -*- Perl -*-

=head1 NAME

elogind git tree checker


=head1 USAGE

check_tree.pl [OPTIONS] <--upstream <path to upstream tree>>


=head1 ARGUMENTS

=over 8

=item B<-u | --upstream>

The path to the upstream tree should have the same layout as the place from
where this program is called. It is best to call this program from the
elogind root path and use a systemd upstream root path for comparison.

=back


=head1 OPTIONS

=over 8

=item B<-h | --help>

This help message. Use twice to show full perldoc page.

=item B<-c|--commit>

Check out <refid> in the upstream tree.

=item B<--create>

Needs --file.
If the file does not exist, create it.

=item B<-f|--file>

Do not search recursively, check only <path>.

For the check of multiple files, you can either specify -f multiple times,
or concatenate paths with  a comma, or mix both methods.

=item B<--stay>

Needs --commit.
Do not reset to the current commit, stay with the wanted commit.

=back


=head1 DESCRIPTION

Check the current tree, from where this program is called, against an upstream tree for changes,
and generate a patchset out of the differences, that does not interfere with elogind development
markings.


=head1 REQUIRED ARGUMENTS

The path to the upstream tree to compare with is the only mandatory argument.


=head1 EXIT STATUS

The tools returns 0 on success and 1 on error.
If you kill the program with any signal that can be caught and handled, it will
do its best to end gracefully, and exit with exit code 42.


=head1 CONFIGURATION

Currently the only supported configuration are the command line arguments.


=head1 DEPENDENCIES

You will need a recent version of git to make use of this tool.


=head1 DIAGNOSTICS

To find issues on odd program behavior, the -D/--debug command line argument can
be used. Please be warned, though, that the program becomes **very** chatty!

=head2 DEBUG MODE

=over 8

=item B<-D | --debug>

Displays extra information on all the steps of the way.
IMPORTANT: _ALL_ temporary files are kept! Use with caution!

=back


=head1 INCOMPATIBILITIES

None known at the moment.


=head1 BUGS AND LIMITATIONS

Currently none known.

Please report bugs and/or errors at:
git@github.com:Yamakuzure/pwx-elogind-migration-tools/issues


=head1 AUTHOR

Sven Eden <sven@eden-worx.com>


=head1 LICENSE AND COPYRIGHT

Copyright (C) 2017 Sven Eden, EdenWorX

This program is free software: you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

This program is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with
this program. If not, see https://www.gnu.org/licenses/.


=cut
