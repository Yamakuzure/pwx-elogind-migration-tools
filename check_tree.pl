#!/usr/bin/perl -w
use strict;
use warnings FATAL => 'all';

use Carp;
use Cwd qw( getcwd abs_path );
use File::Basename;
use File::Find;
use Getopt::Long;
use Git::Wrapper;
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
#
# ========================
# === Little TODO list ===
# ========================
#
# ...nothing right now...
#
# ------------------------
## Please keep this current!
Readonly our $VERSION => "1.4.2";

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
Readonly my $PROGDIR => dirname($0);
Readonly my $WORKDIR => getcwd();

# ================================================================
# ===        ==> ------ Constants and Helpers ----- <==        ===
# ================================================================
Readonly my $AT             => q{@};
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
Readonly my $SLASH          => q{/};
Readonly my $SPACE          => q{ };
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
	"shell" => [
		'LINGUAS',           'Makefile',    'meson', '\.gitignore$', '\.gperf$', '\.in$',       '\.m4$',         '\.pl$',
		'\.po$',             '\.pot$',      '\.py$', '\.sh$',        '\.sym$',   'bash/busctl', 'bash/loginctl', 'pam.d/other',
		'pam.d/system-auth', 'zsh/_busctl', 'zsh/_loginctl'
	],
	"xml" => [ '\.xml$', '\.ent\.in$', '\.policy\.in$/' ]
);

# And some protected website URLs
Readonly my %SYSTEMD_URLS => (
	'fedoraproject.org/projects/systemd' => 1,
	'freedesktop.org/software/systemd'   => 1
);

# ================================================================
# ===        ==> -------- Global variables -------- <==        ===
# ================================================================
my $do_create       = 0;   ## If set to 1, a non-existing file is created.
my $do_stay         = 0;   ## If set to 1, the previous commit isn't restored on exit.
my $file_fmt        = "";  ## Format string built from the longest file name in generate_file_list().
my $have_wanted     = 0;   ## Helper for finding relevant files (see wanted())
my %hToCreate       = ();  ## The keys are files that do not exist and shall be created.
my %hWanted         = ();  ## Helper hash for finding relevant files (see wanted())
my $in_else_block   = 0;   ## Set to 1 if we switched from mask/unmask to 'else'.
my $in_glibc_block  = 0;   ## Set to 1 if we enter a __GLIBC__ block
my $in_mask_block   = 0;   ## Set to 1 if we entered an elogind mask block
my $in_insert_block = 0;   ## Set to 1 if we entered an elogind addition block
my @only_here       = ();  ## List of files that do not exist in $upstream_path.
my $previous_commit = "";  ## Store current upstream state, so we can revert afterwards.
my $show_help       = 0;
my @source_files    = ();  ## Final file list to process, generated in in generate_file_list().
my $upstream_path   = "";
my $wanted_commit   = "";
my @wanted_files    = ();  ## User given file list (if any) to limit generate_file_list()

# ================================================================
# ===        ==> ------- MAIN DATA STRUCTURES ------ <==       ===
# ================================================================
my %hFile = ();  ## Main data structure to manage a complete compare of two files. (See: build_hFile() )

# Note: %hFile is used globally for each file that is processed.
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
my $hHunk = {};  ## Secondary data structure to describe one diff hunk.            (See: build_hHunk() )

# Note: $hHunk is used globally for each Hunk that is processed and points to the
#       current $hFile{hunks}[] instance.
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
my %hIncs = ();  ## Hash for remembered includes over different hunks.

# Note: Only counted in the first step, actions are only in the second step.
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
my %hProtected = ();  ## check_name_reverts() writes notes down lines here, which check_comments() shall not touch
my @lFails     = ();  ## List of failed hunks. These are worth noting down in an extra structure, as these

# mean that something is fishy about a file, like elogind mask starts within masks.
# The structure is:
# ( { hunk : the failed hunk for later printing
#     msg  : a message set by the function that failed
#     part : local relative file part
#   }
# )

# ================================================================
# ===        ==> --------  Function list   -------- <==        ===
# ================================================================
sub build_hFile;         ## Initializes and fills %hFile.
sub build_hHunk;         ## Adds a new $hFile{hunks}[] instance.
sub build_output;        ## Writes $hFile{output} from all useful $hFile{hunks}.
sub check_blanks;        ## Check that useful blank line additions aren't misplaced.
sub check_comments;      ## Check comments we added for elogind specific information.
sub check_debug;         ## Check for debug constructs
sub check_empty_masks;   ## Check for empty mask blocks, remove them and leave a note.
sub check_func_removes;  ## Check for attempts to remove elogind_*() special function calls.
sub check_includes;      ## performe necessary actions with the help of %hIncs (built by read_includes())
sub check_masks;         ## Check for elogind preprocessor masks
sub check_musl;          ## Check for musl_libc compatibility blocks
sub check_name_reverts;  ## Check for attempts to revert 'elogind' to 'systemd'
sub check_stdc_version;  ## Check for removal of a dfined(__STDC_VERSION) guard
sub check_sym_lines;     ## Check for attempts to uncomment unsupported API functions in .sym files.
sub check_useless;       ## Check for useless updates that do nothing.
sub checkout_upstream;   ## Checkout the given refid on $upstream_path
sub clean_hFile;         ## Completely clean up the current %hFile data structure.
sub diff_hFile;          ## Generates the diff and builds $hFile{hunks} if needed.
sub get_hunk_head;       ## Generate the "@@ -xx,n +yy,m @@" hunk header line out of $hHunk.
sub hunk_failed;         ## Generates a new @lFails entry and terminates the progress line.
sub hunk_is_useful;      ## Prunes the hunk and checks whether it stil does anything
sub is_insert_end;       ## Return 1 if the argument consists of any insertion end
sub is_insert_start;     ## Return 1 if the argument consists of any insertion start
sub is_mask_else;        ## Return 1 if the argument consists of any mask else
sub is_mask_end;         ## Return 1 if the argument consists of any mask end
sub is_mask_start;       ## Return 1 if the argument consists of any mask start
sub prepare_shell;       ## Prepare shell (and meson) files for our processing
sub prepare_xml;         ## Prepare XML files for our processing (Unmask double dashes in comments)
sub protect_config;      ## Special function to not let diff add unwanted or remove our lines in logind.conf.in
sub prune_hunk;          ## remove unneeded prefix and postfix lines.
sub read_includes;       ## map include changes
sub splice_includes;     ## Splice all includes that were marked for splicing
sub unprepare_shell;     ## Unprepare shell (and meson) files after our processing
sub unprepare_xml;       ## Unprepare XML files after our processing (Mask double dashes in comments)

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
log_status("Program Start");
if ( ( length $wanted_commit ) > 0 ) {
	checkout_upstream($wanted_commit)  ## Note: Does nothing if $wanted_commit is already checked out.
	        or exit 1;
}
generate_file_list() or exit 1;            ## Note: @wanted_files is heeded.

# ================================================================
# ===        ==> -------- = MAIN PROGRAM = -------- <==        ===
# ================================================================

for my $file_part (@source_files) {

	# Pre-exit, check for a signal.
	( $death_note > 0 ) and next;  ## No display, we already have the cancellation msg out!

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
	for ( my $pos = 0 ; $pos < $hFile{count} ; ++$pos ) {

		# Break off if a signal was caught
		( $death_note > 0 ) and ( $pos = $hFile{count} ) and next;

		log_debug( "Checking Hunk %d", $pos + 1 );
		$hHunk = $hFile{hunks}[$pos];  ## Global shortcut

		# === Special 1) protect src/login/logind.conf.in =================
		if ( $hFile{source} =~ m/src\/login\/logind[${DOT}]conf[${DOT}]in/msx ) {
			protect_config() and hunk_is_useful() and prune_hunk() or next;
		}

		# === 1) Check for elogind masks 1 (normal source code) ===========
		check_masks() and hunk_is_useful() and prune_hunk() or next;

		# === 2) Check for elogind masks 2 (symbol files) =================
		check_sym_lines() and hunk_is_useful() and prune_hunk() or next;

		# === 3) Check for musl_libc compatibility blocks =================
		check_musl() and hunk_is_useful() and prune_hunk() or next;

		# === 4) Check for __STDC_VERSION guard removals ==================
		check_stdc_version() and hunk_is_useful() and prune_hunk() or next;

		# === 5) Check for debug constructs ===============================
		check_debug() and hunk_is_useful() and prune_hunk() or next;

		# === 6) Check for useful blank line additions ====================
		check_blanks() and hunk_is_useful() and prune_hunk() or next;

		# === 7) Check for 'elogind' => 'systemd' reverts =================
		%hProtected = ();
		check_name_reverts() and hunk_is_useful() and prune_hunk() or next;

		# === 8) Check for elogind_*() function removals ==================
		check_func_removes() and hunk_is_useful() and prune_hunk() or next;

		# === 9) Check for elogind extra comments and information =========
		check_comments() and hunk_is_useful() and prune_hunk() or next;

		# === 10) Check for any useless changes that do nothing ============
		check_useless() and hunk_is_useful() and prune_hunk() or next;

		# === 11) Check for empty masks that guard nothing any more =======
		check_empty_masks() and hunk_is_useful() and prune_hunk() or next;

		#  ===> IMPORTANT: From here on no more pruning, lines must *NOT* change any more! <===

		# === 11) Analyze includes and note their appearance in $hIncs =====
		read_includes();  ## Never fails, doesn't change anything.

	} ## end for ( my $pos = 0 ; $pos...)

	# Break off if a signal was caught
	( $death_note > 0 ) and show_progress( 1, "$file_fmt : cancelled", $file_part ) and next;

	# ---------------------------------------------------------------------
	# --- Make sure saved include data is sane                          ---
	# ---------------------------------------------------------------------
	for my $inc ( keys %hIncs ) {
		$hIncs{$inc}{applied} = 0;
		defined( $hIncs{$inc}{elogind} )
		        or $hIncs{$inc}{elogind} = { hunkid => -1, lineid => -1 };
		defined( $hIncs{$inc}{insert} )
		        or $hIncs{$inc}{insert} = { elogind => 0, hunkid => -1, lineid => -1, spliceme => 0, sysinc => 0 };
		defined( $hIncs{$inc}{remove} )
		        or $hIncs{$inc}{remove} = { hunkid => -1, lineid => -1, sysinc => 0 };
	} ## end for my $inc ( keys %hIncs)

	# ---------------------------------------------------------------------
	# --- Go through all hunks and apply remaining changes and checks   ---
	# ---------------------------------------------------------------------
	for ( my $pos = 0 ; $pos < $hFile{count} ; ++$pos ) {
		$hHunk = $hFile{hunks}[$pos];  ## Global shortcut

		# (pre -> early out)
		hunk_is_useful() or next;

		# === 1) Apply what we learned about changed includes =============
		check_includes() and hunk_is_useful() or next;

	} ## end for ( my $pos = 0 ; $pos...)

	# ---------------------------------------------------------------------
	# --- Splice all include insertions that are marked for splicing    ---
	# ---------------------------------------------------------------------
	splice_includes();

	# ---------------------------------------------------------------------
	# --- Go through all hunks for a last prune and check               ---
	# ---------------------------------------------------------------------
	my $have_hunk = 0;
	for ( my $pos = 0 ; $pos < $hFile{count} ; ++$pos ) {
		$hHunk = $hFile{hunks}[$pos];  ## Global shortcut

		# (pre -> early out)
		hunk_is_useful() or next;

		prune_hunk() and ++$have_hunk;
	} ## end for ( my $pos = 0 ; $pos...)

	# If we have at least 1 useful hunk, create the output and tell the user what we've got.
	$have_hunk
	        and build_output()  # (Always returns 1)
	        and show_progress( 1, "$file_fmt: %d Hunk%s", $file_part, $have_hunk, $have_hunk > 1 ? "s" : "" )
	        or show_progress( 1, "$file_fmt: clean", $file_part );

	# Shell and xml files must be unprepared. See unprepare_[shell,xml]()
	$hFile{pwxfile} and ( unprepare_shell() or unprepare_xml() );

	# Now skip the writing if there are no hunks
	$have_hunk or next;

	# That's it, write the file and be done!
	if ( open( my $fOut, ">", $hFile{patch} ) ) {
		for my $line ( @{ $hFile{output} } ) {

			# Do not assume empty comment lines with trailing spaces in shell files
			$hFile{pwxfile} and $line =~ s/([+ -][${HASH}])\s+$/$1/msgx;
			print $fOut "$line\n";
		} ## end for my $line ( @{ $hFile...})
		close($fOut);
	} else {
		log_error( "ERROR: %s could not be opened for writing!\n%s\n", $hFile{patch}, $! );
		confess("Please fix this first!");
	}
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
	if ( scalar @only_here ) {
		my $count = scalar @only_here;
		my $fmt   = sprintf( "%%d %d: %%s", length("$count") );

		log_info( "\n%d file%s only found in $WORKDIR:", $count, $count > 1 ? "s" : "" );

		for ( my $i = 0 ; $i < $count ; ++$i ) {
			log_info( $fmt, $i + 1, $only_here[$i] );
		}
	} ## end if ( scalar @only_here)

	# -------------------------------------------------------------------------
	# --- Print out the list of failed hunks -> bug in hunk or program?     ---
	# -------------------------------------------------------------------------
	if ( scalar @lFails ) {
		my $count = scalar @lFails;

		log_warning( "\n%d file%s %s at least one fishy hunk:", $count, $count > 1 ? "s" : "", $count > 1 ? "have" : "has" );

		for ( my $i = 0 ; $i < $count ; ++$i ) {
			log_warning("=== $lFails[$i]{part} ===");
			log_warning(" => $lFails[$i]{msg} <=");
			log_warning("---------------------------");
			log_warning( " {count}        : \"" . $lFails[$i]{info}{count} . "\"" );
			log_warning( " {idx}          : \"" . $lFails[$i]{info}{idx} . "\"" );
			log_warning( " {masked_end}   : \"" . $lFails[$i]{info}{masked_end} . "\"" );
			log_warning( " {masked_start} : \"" . $lFails[$i]{info}{masked_start} . "\"" );
			log_warning( " {offset}       : \"" . $lFails[$i]{info}{offset} . "\"" );
			log_warning( " {src_start}    : \"" . $lFails[$i]{info}{src_start} . "\"" );
			log_warning( " {tgt_start}    : \"" . $lFails[$i]{info}{tgt_start} . "\"" );
			log_warning( " {useful}       : \"" . $lFails[$i]{info}{useful} . "\"" );
			log_warning("---------------------------");
			log_warning("$_\n") foreach ( @{ $lFails[$i]{hunk} } );
		} ## end for ( my $i = 0 ; $i < ...)
	} ## end if ( scalar @lFails )

	$do_stay or length($previous_commit) and checkout_upstream($previous_commit);

	log_status("Program End");
} ## end END

# ================================================================
# ===        ==> ---- Function Implementations ---- <==        ===
# ================================================================

# -----------------------------------------------------------------------
# --- Initializes and fills %hFile. Old values are discarded.         ---
# --- Adds files, that do not exist upstream, to @only_here.          ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub build_hFile {
	my ($part) = @_;

	defined($part) and length($part) or log_error("ERROR") and confess("build_hfile: part is empty ???");

	# Is this a new file?
	my $isNew = defined( $hToCreate{$part} ) ? 1 : 0;

	# We only prefixed './' to unify things. Now it is no longer needed:
	$part =~ s,^\./,,;

	# Pre: erase current $hFile, as that is what is expected.
	clean_hFile();

	# Check the target file
	my $tgt = "$upstream_path/$part";
	$tgt =~ s/elogind/systemd/msg;
	$tgt =~ s/\.pwx$//;
	-f $tgt
	        or push( @only_here, $part )
	        and return 0;

	# Build the patch name
	my $patch = $part;
	$patch =~ s/\//_/msg;

	# Determine whether this is a shell or xml file needing preparations.
	my $is_sh  = 0;
	my $is_xml = 0;
	for my $pat ( @{ $FILE_NAME_PATTERNS{"xml"} } ) {
		$part =~ m/$pat/ and $is_xml = 1 and last;
	}
	if ( 0 == $is_xml ) {
		for my $pat ( @{ $FILE_NAME_PATTERNS{"shell"} } ) {
			$part =~ m/$pat/ and $is_sh = 1 and last;
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

# -----------------------------------------------------------------------
# --- Build a new $hHunk instance and add it to $hFile{hunks}         ---
# -----------------------------------------------------------------------
sub build_hHunk {
	my ( $head, @lHunk ) = @_;
	my $pos  = $hFile{count}++;
	my $mark = qq<[${AT}]{2}>;

	# The first line must be the hunk positional and size data.
	# example: @@ -136,6 +136,8 @@
	# That is @@ -<source line>,<source length> +<target line>,<target length> @@
	if ( $head =~ m/^${mark}\s+-(\d+),\d+\s+\+(\d+),\d+\s+${mark}/msx ) {
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
			defined($line) or next;
			chomp $line;
			push @{ $hFile{hunks}[$pos]{lines} }, $line;
			$hFile{hunks}[$pos]{count}++;
		} ## end for my $line (@lHunk)
		return 1;
	} ## end if ( $head =~ m/^${mark}\s+-(\d+),\d+\s+\+(\d+),\d+\s+${mark}/msx)

	log_error( "Illegal hunk no %d\n(Head: \"%s\")\nIgnoring...", $hFile{count}, $head );
	$hFile{count}--;

	return 0;
} ## end sub build_hHunk

# -----------------------------------------------------------------------
# --- Writes $hFile{output} from all useful $hFile{hunks}.            ---
# --- Important: No more checks, just do it!                          ---
# -----------------------------------------------------------------------
sub build_output {

	my $offset = 0;  ## Count building up target offsets

	for ( my $pos = 0 ; $pos < $hFile{count} ; ++$pos ) {
		$hHunk = $hFile{hunks}[$pos];  ## Global shortcut

		# The useless are to be skipped, but we need the hunks masked_end
		if ( $hHunk->{useful} ) {

			# --- Note down the relevant starting mask status ---
			# ---------------------------------------------------
			defined( $hHunk->{masked_start} ) and ( 1 == length("$hHunk->{masked_start}") )
			        or return hunk_failed(
				"build_output: Hunk "
				        . (
					defined( $hHunk->{masked_start} )
					? "with \"" . $hHunk->{masked_start} . "\""
					: "without"
				        )
				        . " masked_start key found!"
			        );
			$hFile{pwxfile} and push( @{ $hFile{output} }, "# masked_start " . $hHunk->{masked_start} );

			# --- Add the header line ---------------------------
			# ---------------------------------------------------
			push( @{ $hFile{output} }, get_hunk_head( \$offset ) );

			# --- Add the hunk lines ----------------------------
			# ---------------------------------------------------
			for my $line ( @{ $hHunk->{lines} } ) {
				push( @{ $hFile{output} }, $line );
			}
		} ## end if ( $hHunk->{useful} )

		# --- Note down the relevant ending mask status -----
		# ---------------------------------------------------
		defined( $hHunk->{masked_end} ) and ( 1 == length("$hHunk->{masked_end}") )
		        or return hunk_failed(
			"build_output: Hunk "
			        . (
				defined( $hHunk->{masked_end} )
				? "with \"" . $hHunk->{masked_end} . "\""
				: "without"
			        )
			        . " masked_end key found!"
		        );
		$hFile{pwxfile} and push( @{ $hFile{output} }, "# masked_end " . $hHunk->{masked_end} );

	} ## end for ( my $pos = 0 ; $pos...)

	return 1;
} ## end sub build_output

sub change_analyze_hunk_line {
	my ( $pChanges, $line_idx, $text, $is_masked ) = @_;
	my $prefix       = $EMPTY;
	my $comment_str  = $EMPTY;
	my $replace_text = $EMPTY;
	my $areas        = q{elogind|loginctl|systemctl|systemd};
	my $source_str   = $EMPTY;

	if ( $text =~ m/^([${PLUS}${SPACE}${DASH}])\s*([${HASH}${SLASH}*]*)\s*(.*(${areas}).*)\s*[*${SLASH}${HASH}]*\s*$/misx ) {
		$prefix       = $1;
		$comment_str  = strempty($2);
		$replace_text = $3;
		$source_str   = lc($4);
	} else {
		return 0;  # Other lines are of no concern
	}

	# Initialize the change entry if there is  yet
	if ( !( defined $pChanges->{'texts'}{$replace_text} ) ) {
		$pChanges->{'texts'}{$replace_text} = { 'count' => 0, 'changes' => [] };
	}

	# We need a few values...
	my $i = $pChanges->{$replace_text}{'count'} // 0;  # The count is the next free index
	my $kind =
	          ( 'elogind' eq $source_str )   ? $KIND_ELOGIND
	        : ( 'loginctl' eq $source_str )  ? $KIND_LOGINCTL
	        : ( 'systemd' eq $source_str )   ? $KIND_SYSTEMD
	        : ( 'systemctl' eq $source_str ) ? $KIND_SYSTEMCTL
	        :                                  0;
	my $type   = ( '-' eq $prefix ) ? $TYPE_REMOVAL : ( '+' eq $prefix ) ? $TYPE_ADDITION : $TYPE_NEUTRAL;
	my $alttxt = change_find_alt_text( $kind, $replace_text );
	my $iscomment =
	          ( ( $comment_str =~ m/^[$HASH]+$/msx ) && $hFile{'is_sh'} )  ? $TRUE
	        : ( ( $comment_str =~ m/^[\/*]+$/ )      && !$hFile{'is_sh'} ) ? $TRUE
	        :                                                                $FALSE;

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

	log_debug( "%-8s type %d at line % 3d: \"%s\"", ( 0 > $type ) ? 'REMOVAL' : ( 0 < $type ) ? 'ADDITION' : 'Neutral', $kind, $line_idx + 1, $replace_text );

	return 1;
} ## end sub change_analyze_hunk_line

sub change_check_next_partner {
	my ( $change, $next_partner, $partner_p, $prev_partner_p ) = @_;
	my $kind         = change_get_partner_kind( $change->{'kind'} );
	my $partner_line = ( defined ${$partner_p} ) ? ${$partner_p}->{'line'} : -1;  ## To ensure not to shuffle partner relations
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

sub change_check_solo_changes {
	my ($pChanges) = @_;

	foreach my $change ( grep { defined $_ } @{ $pChanges->{'lines'} } ) {

		# change is now a reference into $pChange, explicitly at
		#    $pChanges->{string}{'texts'}{'changes'}[no]
		# and has write-back capabilities.

		log_change( 'Handle Solo Changes ; Considering Change', $change,              0 );
		log_change( '--- ==> Partner : ---',                    $change->{'partner'}, 1 );

		# If the change is already finished, or if it has a partner defined, nothing is to be done.
		( ( $TRUE == $change->{'done'} ) || ( defined $change->{'partner'} ) ) and next;

		# If it is removed from or added to a mask block, we are ok with it
		( $TRUE == $change->{'masked'} ) and change_mark_as_done($change) and next;

		# We have only checked pretexted text additions, yet, not singular removals
		change_is_protected_text( $change->{'text'}, $change->{'iscomment'} ) and change_mark_as_done($change) and next;

		if ( $TYPE_ADDITION == $change->{'type'} ) {

			# Replace the non-protected systemd phrases with our elogind alternative.
			if ( ( ( length $change->{'alttxt'} ) > 0 ) && ( $change->{'systemd'} > 0 ) ) {
				log_debug( "     => Replacing \"%s\"", $change->{'text'} );
				log_debug( "     => with      \"%s\"", $change->{'alttxt'} );
				$change->{'text'} = $change->{'alttxt'};
			}
			change_mark_as_done($change);
			next;
		} ## end if ( $TYPE_ADDITION ==...)

		if ( $TYPE_REMOVAL == $change->{'type'} ) {

			# Undo elogind removals, those are probably our own elogind-exclusive functions
			if ( 1 == $change->{'elogind'} ) {
				substr( $hHunk->{lines}[ $change->{'line'} ], 0, 1 ) = " ";
				log_debug( "     => Keeping   \"%s\"", $hHunk->{lines}[ $change->{'line'} ] );
			}
			change_mark_as_done($change);
		} ## end if ( $TYPE_REMOVAL == ...)
	} ## end foreach my $change ( grep {...})

	return 1;
} ## end sub change_check_solo_changes

sub change_find_alt_text {
	my ( $source_kind, $source_text ) = @_;
	my $alt = $source_text;

	log_debug( "Searching alt text for source kind %d:", $source_kind );
	log_debug( " txt: \"%s\"",                           $source_text );

	# 1) 'elogind' => 'systemd'
	if ( $KIND_ELOGIND == $source_kind ) {
		$alt =~ s/elogind/systemd/msgx;
		$source_text eq $alt and $alt =~ s/ELOGIND/SYSTEMD/msgx;   ## Try uppercase alternative
		$source_text eq $alt and $alt =~ s/elogind/systemd/misgx;  ## Try caseless alternative

		# Note: The replacement of 'systemd-logind' or 'systemd-stable' with elogind can not be reversed this way.
		#       The usr of this subs result (change_map_hunk_lines()) has to do this itself when searching for a match.
	} ## end if ( $KIND_ELOGIND == ...)

	# 2) 'loginctl' => 'systemctl'
	if ( $KIND_LOGINCTL == $source_kind ) {
		$alt =~ s/loginctl/systemctl/msgx;
		$source_text eq $alt and $alt =~ s/LOGINCTL/SYSTEMCTL/msgx;   ## Try uppercase alternative
		$source_text eq $alt and $alt =~ s/loginctl/systemctl/misgx;  ## Try caseless alternative
	}

	# 3) 'systemd' => 'elogind'
	if ( $KIND_SYSTEMD == $source_kind ) {
		$alt =~ s/systemd[-_]logind/elogind/msgx;
		$source_text eq $alt and $alt =~ s/systemd[-_]stable/elogind/msgx;  ## Try the stable alternative
		$source_text eq $alt and $alt =~ s/systemd/elogind/msgx;            ## Try plain alternative
		$source_text eq $alt and $alt =~ s/SYSTEMD/ELOGIND/msgx;            ## Try uppercase alternative
		$source_text eq $alt and $alt =~ s/systemd/elogind/misgx;           ## Try caseless alternative

		# If we are in a man page, systemd is placed in volume 1, while elogind is placed in volume 8
		$source_text ne $alt and $alt =~ s/<manvolnum>1<\/manvolnum>/<manvolnum>8<\/manvolnum>/msgx;
	} ## end if ( $KIND_SYSTEMD == ...)

	# 4) 'systemctl' => 'loginctl'
	if ( $KIND_SYSTEMCTL == $source_kind ) {
		$alt =~ s/systemctl/loginctl/msgx;
		$source_text eq $alt and $alt =~ s/SYSTEMCTL/LOGINCTL/msgx;         ## Try uppercase alternative
		$source_text eq $alt and $alt =~ s/systemctl/loginctl/misgx;        ## Try caseless alternative
	}

	# In some meson files, we need the variable "systemd_headers".
	# This refers to the systemd API headers that get installed,
	# and must therefore not be renamed to elogind_headers.
	$alt =~ s/elogind_headers/systemd_headers/msg;

	# systemd-sleep.conf is *not* elogind-sleep.conf, but just sleep.conf in elogind
	$alt =~ s/(?:systemd|elogind)${DASH}(sleep${DOT}conf)/$1/msgx;

	my $alttxt = ( $alt eq $source_text ) ? $EMPTY : $alt;
	log_debug( " alt: \"%s\"", ( ( length $alttxt ) > 0 ) ? $alttxt : 'n/a' );

	return $alttxt;
} ## end sub change_find_alt_text

# @brief Scan the change hash for a partner to the given change
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
	my $partner      = $change->{'partner'};  ## The last partner found
	my $prev_partner = undef;                 ## The previous partner found

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
	( defined $partner ) or return 1;              ## Nothing to do

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

sub change_get_line_index {
	my ( $pChanges, $line_no, $count ) = @_;
	for ( my $i = 0 ; ( $i < $count ) ; ++$i ) {
		( defined $pChanges->[$i] ) and ( defined $pChanges->[$i]{'line'} ) and ( $line_no == $pChanges->[$i]{'line'} ) and return $i;
	}
	return -1;
} ## end sub change_get_line_index

sub change_get_partner_kind {
	my ($kind) = @_;

	( $KIND_SYSTEMD == $kind )   and return $KIND_ELOGIND;
	( $KIND_SYSTEMCTL == $kind ) and return $KIND_LOGINCTL;
	( $KIND_ELOGIND == $kind )   and return $KIND_SYSTEMD;
	( $KIND_LOGINCTL == $kind )  and return $KIND_SYSTEMCTL;

	croak("change_get_partner_kind() called with invalid kind '$kind'!");
} ## end sub change_get_partner_kind

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
		( $change->{'line'} > $partner->{'line'} ) or next;  ## change_handle_removals() takes care of forward removals.

		# If they are direct renames, undo them if they go from elogind to systemd, but accept if it is the other way round
		if ( $change->{'line'} == ( $partner->{'line'} + 1 ) ) {
			( $TRUE == $change->{'systemd'} ) and change_undo( $partner, $change, $i );

			# No change for the other way around, just mark as done
			change_mark_as_done($change);  ## Also marks the partner
			next;
		} ## end if ( $change->{'line'}...)

		# If they are further away, check comment and mask status
		if (       ( ( $TRUE == $partner->{'masked'} ) && ( $FALSE == $change->{'masked'} ) )
			|| ( ( $TRUE == $partner->{'iscomment'} ) && ( $FALSE == $change->{'iscomment'} ) ) )
		{
			## The change moves a masked or commented line out of the mask/comment
			( $TRUE == $change->{'systemd'} )                    #
			        and change_reverse( $partner, $change, $i )  # Apply the elogind->systemd change to the partner, splice the removal
			        or change_undo( $partner, $change, $i );     # Remove the systemd->elogind move, although this seems to be impossibly to ever happen.
			change_mark_as_done($change);                        # Also marks the partner
			next;
		} ## end if ( ( ( $TRUE == $partner...)))

		# In all other cases we allow the move, but reverse the text change if it is elogind->systemd
		( $TRUE == $change->{'systemd'} ) and change_use_alt($change);
		change_mark_as_done($change);                                # Also marks the partner
	} ## end for my $i ( 0 .. $#{$lines_ref...})

	return 1;
} ## end sub change_handle_additions

sub change_handle_false_positives {
	my ($pChanges) = @_;

	foreach my $change ( grep { defined $_ } @{ $pChanges->{'lines'} } ) {

		# change is now a reference into $pChange, explicitly at
		#    $pChanges->{string}{'texts'}{'changes'}[no]
		# and has write-back capabilities.
		( $FALSE == $change->{'done'} ) and ( $TYPE_ADDITION == $change->{'type'} ) or next;  ## Already handled or not an addition
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

		# 3) References to systemd-homed and other tools not shipped by elogind
		#    must not be changed either, or users might think elogind has its
		#    own replacements.
		my $systemd_daemons  = qq{home|import|journal|network|oom|passwor|udev};
		my $systemd_products = qq{analyze|creds|cryptsetup|export|firstboot|fsck|home|import-fs|nspawn|repart|syscfg|sysusers|tmpfiles|devel\/};
		( ( $text =~ m/systemd[-_]($systemd_daemons)d/msx ) || ( $text =~ m/systemd[-_]($systemd_products)/msx ) ) and change_mark_as_done($change) and next;

		# Also the gettext domain is always "systemd", and varlink works via io.systemd domain.
		( ( $text =~ m/gettext-domain="systemd/msx ) || ( $text =~ m/io[.]systemd/msx ) ) and change_mark_as_done($change) and next;
	} ## end foreach my $change ( grep {...})

	return 1;
} ## end sub change_handle_false_positives

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
		( $change->{'line'} > $partner->{'line'} ) or next;  ## change_handle_additions() takes care of forward additions.

		# If they are direct renames, undo them if they go from elogind to systemd, but accept if it is the other way round
		if ( $change->{'line'} == ( $partner->{'line'} + 1 ) ) {
			( $TRUE == $change->{'elogind'} ) and change_undo( $change, $partner, $i );

			# No change for the other way around, just mark as done
			change_mark_as_done($change);  ## Also marks the partner
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

		# In all other cases we allow the move, but reverse the text change if it is elogind->systemd
		( $TRUE == $change->{'elogind'} ) and change_use_alt($partner);
		change_mark_as_done($change);                                # Also marks the partner
	} ## end for my $i ( 0 .. $#{$lines_ref...})

	return 1;
} ## end sub change_handle_removals

sub change_is_protected_text {
	my ( $text, $is_commented ) = @_;

	# 1) /run/systemd/ must not be changed, as other applications
	#    rely on that naming.
	# Note: The /run/elogind.pid file is not touched by that, as
	#       systemd does not have something like that.
	$text =~ m/\/run\/systemd/msx and log_debug( "     => Protected \"%s\"", $text ) and return 1;

	# 2) Several systemd website urls must not be changed, too
	for my $pat ( keys %SYSTEMD_URLS ) {
		$text =~ m/$pat/msx and log_debug( "     => Protected \"%s\"", $text ) and return 1;
	}

	# 3) To be a dropin-replacement, we also need to not change any org[./]freedesktop[./]systemd strings
	$text =~ m/\/?org[.\/]freedesktop[.\/]systemd/msx and log_debug( "     => Protected \"%s\"", $text ) and return 1;

	# 4) Do not replace referrals to systemd[1]
	$text =~ m/systemd\[1\]/msx and log_debug( "     => Protected \"%s\"", $text ) and return 1;

	# 5) Specific systemd services that might be mentioned in comments that are not masked:
	my $systemd_services = qq{user-sessions|logind};
	( $is_commented > 0 ) and ( ( $text =~ m/systemd[-_]($systemd_services)[${DOT}]service/msx ) ) and return 1;

	return 0;
} ## end sub change_is_protected_text

sub change_map_hunk_lines {
	my ($pChanges) = @_;

	# 1) Loop over additions to find previous matching removals
	# -----------------------------------------------------------------------------------------------------------------
	foreach my $change ( grep { defined $_ } @{ $pChanges->{'lines'} } ) {

		# change is now a reference into $pChange, explicitly at
		#    $pChanges->{string}{'texts'}{'changes'}[no]
		# and has write-back capabilities.
		log_change( 'Scanning Additions ; Considering Change', $change, 0 );
		( $FALSE == $change->{'done'} ) and ( $TYPE_ADDITION == $change->{'type'} ) or next;  ## Already handled or not an addition
		( 1 == $change->{'systemd'} )                                               or next;  ## only systemd additions are relevant
		change_find_and_set_partner( $pChanges, $change );
		log_change( 'Scanning Additions ; Change Mapped', $change,              0 );
		log_change( '--- ==> Partner : ---',              $change->{'partner'}, 1 );
	} ## end foreach my $change ( grep {...})

	# We now have mapped regular diffs that remove something on line n and add it back, changed on line n+x.

	# 2) Loop over removals to find previous matching additions
	# -----------------------------------------------------------------------------------------------------------------
	foreach my $change ( grep { defined $_ } @{ $pChanges->{'lines'} } ) {
		log_change( 'Scanning Removals ; Considering Change', $change, 0 );
		( $FALSE == $change->{'done'} ) and ( $TYPE_REMOVAL == $change->{'type'} ) or next;  ## Already handled or not a removal
		( 1 == $change->{'elogind'} )                                              or next;  ## only elogind removals are relevant
		change_find_and_set_partner( $pChanges, $change );
		log_change( 'Scanning Removals ; Change Mapped', $change,              0 );
		log_change( '--- ==> Partner : ---',             $change->{'partner'}, 1 );
	} ## end foreach my $change ( grep {...})

	# The second run mapped real moves, so the line was not only changed, it was also moved
	# At this point we can assume, that unpartnered removals and additions are real changes to the source code and no longer
	# change systemd<->elogind naming only.

	return 1;
} ## end sub change_map_hunk_lines

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
	( $TRUE == $r ) or return $FALSE;  ## Followup from running out of prevs above

	# Now we can move the partner to prev
	$prev->{'partner'}    = $partner;
	$partner->{'partner'} = $prev;
	$change->{'partner'}  = undef;

	return $TRUE;
} ## end sub change_move_partner_up

sub change_reverse {
	my ( $to_change, $to_splice, $at_line ) = @_;

	log_debug( "     => Changing  \"%s\"", $hHunk->{lines}[ $to_change->{'line'} ] );
	change_use_alt($to_change);
	substr( $hHunk->{lines}[ $to_change->{'line'} ], 0, 1 ) = " ";
	$to_splice->{'spliceme'} = $at_line;
	log_debug( "           => To  \"%s\"", $hHunk->{lines}[ $to_change->{'line'} ] );
	log_debug( "     => Splicing  \"%s\"", $hHunk->{lines}[ $to_splice->{'spliceme'} ] );

	return 1;
} ## end sub change_reverse

sub change_splice_the_undone {
	my ($pChanges) = @_;

	# 1) Loop over lines and note down those to be spliced
	# -----------------------------------------------------------------------------------------------------------------
	my %hSplices = ();
	foreach my $change ( grep { defined $_ } @{ $pChanges->{'lines'} } ) {
		( $change->{'spliceme'} > 0 ) or next;
		$hSplices{ $change->{'spliceme'} } = 1;
		log_debug( "Splice line % 3d: \"%s\"", $change->{'spliceme'} + 1, $change->{'text'} );
	}

	# 2) Loop over the splices and remove them, use reverse order to not get confused
	# -----------------------------------------------------------------------------------------------------------------
	for my $l ( sort { $b <=> $a } keys %hSplices ) {
		splice( @{ $hHunk->{lines} }, $l, 1 );
		--$hHunk->{count};
	}

	return 1;
} ## end sub change_splice_the_undone

sub change_undo {
	my ( $to_keep, $to_splice, $at_line ) = @_;

	substr( $hHunk->{lines}[ $to_keep->{'line'} ], 0, 1 ) = " ";
	$to_splice->{'spliceme'} = $at_line;
	log_debug( "     => Keeping  % 3d: \"%s\"", $to_keep->{'line'} + 1, $hHunk->{lines}[ $to_keep->{'line'} ] );
	log_debug( "     => Splicing % 3d: \"%s\"", $at_line + 1,           $hHunk->{lines}[ $to_splice->{'spliceme'} ] );

	return 1;
} ## end sub change_undo

sub change_use_alt {
	my ($change) = @_;
	my $lno      = $change->{'line'};
	my $newText  = $change->{'alttxt'};
	my $oldText  = $change->{'text'};

	log_debug( "     => Change  % 3d: \"%s\"", $lno + 1, $hHunk->{lines}[$lno] );
	$hHunk->{lines}[$lno] =~ s{\Q$oldText\E}{$newText};
	log_debug( "     =>   To    % 3d: \"%s\"", $lno + 1, $hHunk->{lines}[$lno] );

	return 1;
} ## end sub change_use_alt

# -----------------------------------------------------------------------
# --- Check that useful blank line additions aren't misplaced.        ---
# ---- Note: Sometimes the masks aren't placed correctly, and the diff---
# ----       wants to add a missing blank line. As it tried to remove ---
# ----       our mask first, it'll be added after. That's fine for    ---
# ----       #endif, but not for #if 0.                               ---
# ----       At the same time, removal of one blank line after our    ---
# ----       endif is also not in order.                              ---
# -----------------------------------------------------------------------
sub check_blanks {

	# early exits:
	defined($hHunk)  or return 0;
	$hHunk->{useful} or return 0;

	log_debug("Checking useful blank additions ...");

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# Check for misplaced addition
		if (       ( $$line =~ m/^[${PLUS}]\s*$/ )
			&& ( $i > 0 )
			&& ( ( is_mask_start( $hHunk->{lines}[ $i - 1 ] ) || is_insert_start( $hHunk->{lines}[ $i - 1 ] ) ) ) )
		{
			# Simply swap the lines
			my $tmp = $$line;
			$$line = $hHunk->{lines}[ $i - 1 ];
			$hHunk->{lines}[ $i - 1 ] = $tmp;
			next;
		} ## end if ( ( $$line =~ m/^[${PLUS}]\s*$/...))

		# Check for unpleasant removals
		if (       ( $$line =~ m/^\-\s*$/ )
			&& ( $i > 0 )
			&& ( ( is_mask_end( $hHunk->{lines}[ $i - 1 ] ) || is_insert_end( $hHunk->{lines}[ $i - 1 ] ) ) )
			&& ( $i < ( $hHunk->{count} - 1 ) )
			&& ( !( $hHunk->{lines}[ $i + 1 ] =~ m/^[-+ ]\s*$/ ) ) )
		{
			# Revert the removal
			substr( $$line, 0, 1 ) = " ";
			next;
		} ## end if ( ( $$line =~ m/^\-\s*$/...))

	} ## end for ( my $i = 0 ; $i < ...)

	return 1;
} ## end sub check_blanks

# -----------------------------------------------------------------------
# --- Check comments we added for elogind specific information.       ---
# --- These are all comments, and can be both single and multi line.  ---
# -----------------------------------------------------------------------
sub check_comments {

	# early exits:
	defined($hHunk)  or return 0;
	$hHunk->{useful} or return 0;

	log_debug("Checking comments...");

	my $in_comment_block = 0;

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# Ignore protected lines
		defined( $hProtected{$$line} ) and next;

		# Check for comment block start
		# -----------------------------
		if ( $$line =~ m/^[${DASH}]\s*(\/\*+|\/\/+)\s+.*elogind/msx ) {

			# Sanity check:
			$in_comment_block
			        and return hunk_failed("check_comments: Comment block start found in comment block!");

			# Only start the comment block if this is really a multiline comment
			( ( $$line =~ m/^[${DASH}]\s*\/\*+/msx ) && !( $$line =~ m/\*\/[^\/]*$/msx ) )
			        and $in_comment_block = 1;

			# Revert the substract *if* this is not in a mask block
			$in_mask_block and ( 1 > $in_else_block ) or substr( $$line, 0, 1 ) = " ";

			next;
		} ## end if ( $$line =~ m/^[${DASH}]\s*(\/\*+|\/\/+)\s+.*elogind/msx)

		# Check for comment block end
		# -----------------------------
		if ( $in_comment_block && ( $$line =~ m/^[${DASH}].*\*\/\s*$/msx ) ) {
			substr( $$line, 0, 1 ) = " ";
			$in_comment_block = 0;
			next;
		}

		# Check for comment block line
		# -----------------------------
		if ( $in_comment_block && ( $$line =~ m/^[${DASH}]/msx ) ) {

			# Note: We do not check for anything else, as empty lines must be allowed.
			substr( $$line, 0, 1 ) = " ";
			next;
		} ## end if ( $in_comment_block...)

		# If none of the above applied, the comment block is over.
		$in_comment_block = 0;
	} ## end for ( my $i = 0 ; $i < ...)

	return 1;
} ## end sub check_comments

# -----------------------------------------------------------------------
# --- Check for debug constructs                                      ---
# --- Rules: ENABLE_DEBUG_ELOGIND must be taken like #if 1, *but*     ---
# ---        here an #else is valid and must stay fully.              ---
# ---        Further there might be multiline calls to                ---
# ---        log_debug_elogind() that must not be removed either.     ---
# -----------------------------------------------------------------------
sub check_debug {

	# early exits:
	defined($hHunk)  or return 0;
	$hHunk->{useful} or return 0;

	log_debug("Checking debug constructs ...");

	# Count non-elogind block #ifs. This is needed, so normal
	# #if/#else/#/endif constructs can be put inside both the
	# debug and the release block.
	my $regular_ifs   = 0;
	my $is_debug_func = 0;  ## Special for log_debug_elogind()

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# entering a debug construct block
		# ---------------------------------------
		if ( $$line =~ m/^-[${HASH}]if.+ENABLE_DEBUG_ELOGIND/msx ) {
			## Note: Here it is perfectly fine to be in an elogind mask or insert block.
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_insert_block++;            ## Increase instead of setting this to 1.
			next;
		} ## end if ( $$line =~ m/^-[${HASH}]if.+ENABLE_DEBUG_ELOGIND/msx)

		# Count regular #if
		$$line =~ m/^-[${HASH}]if/msx and ++$regular_ifs;

		# Switching to the release variant.
		# ---------------------------------------
		if ( ( $$line =~ m/^-[${HASH}]else/msx ) && $in_insert_block && !$regular_ifs ) {
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_else_block++;              ## Increase instead of setting this to 1.
			next;
		}

		# ending a debug construct block
		# ---------------------------------------
		if ( $$line =~ m/^[${DASH}][${HASH}]endif\s*\/\/\/?.*ENABLE_DEBUG_/msx ) {
			( !$in_insert_block )
			        and return hunk_failed("check_debug: #endif // ENABLE_DEBUG_* found outside any debug construct");
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_insert_block--;            ## Decrease instead of setting to 0. This allows such
			$in_else_block--;              ## blocks to reside in regular elogind mask/insert blocks.
			next;
		} ## end if ( $$line =~ m/^[${DASH}][${HASH}]endif\s*\/\/\/?.*ENABLE_DEBUG_/msx)

		# end regular #if
		# ---------------------------------------
		$$line =~ m/^-[${HASH}]endif/msx and --$regular_ifs;

		# Check for log_debug_elogind()
		# ---------------------------------------
		if ( $$line =~ m/^-.*log_debug_elogind\s*\(/msx ) {
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$$line =~ m/\)\s*;/ or ++$is_debug_func;
			next;
		}

		# Remove '-' prefixes in all lines within the debug construct block
		# -------------------------------------------------------------------
		if ( ( $$line =~ m,^[${DASH}], ) && ( $in_insert_block || $is_debug_func ) ) {
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			                               # Note: Everything in *any* insert block must not be removed anyway.
		}

		# Check for the end of a multiline log_debug_elogind() call
		# ---------------------------------------------------------
		$is_debug_func and $$line =~ m/\)\s*;/ and --$is_debug_func;

	} ## end for ( my $i = 0 ; $i < ...)

	return 1;
} ## end sub check_debug

# -----------------------------------------------------------------------
# --- Check for attempts to remove elogind_*() special function calls. --
# --- We have some special functions, needed only by elogind.         ---
# --- One of the most important ones is elogind_set_program_name(),   ---
# --- which has an important role in musl_libc compatibility.         ---
# --- These calls must not be removed of course.                      ---
# -----------------------------------------------------------------------
sub check_func_removes {

	# early exits:
	defined($hHunk)  or return 1;
	$hHunk->{useful} or return 1;

	# Not used in pwx files (meson, xml, sym)
	$hFile{pwxfile} and return 1;

	log_debug("Checking function removals ...");

	# Needed for multi-line calls
	my $is_func_call = 0;

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# Ignore protected lines
		defined( $hProtected{$$line} ) and next;

		# Check for elogind_*() call
		# -------------------------------------------------------------------
		if ( $$line =~ m/^-.*elogind_\S+\s*\(/msx ) {
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$$line =~ m/\)\s*;/ or ++$is_func_call;
			next;
		}

		# Remove '-' prefixes in all lines that belong to an elogind_*() call
		# -------------------------------------------------------------------
		if ( ( $$line =~ m,^[${DASH}], ) && $is_func_call ) {
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
		}

		# Check for the end of a multiline elogind_*() call
		# -------------------------------------------------------------------
		$is_func_call and $$line =~ m/\)\s*;/ and --$is_func_call;
	} ## end for ( my $i = 0 ; $i < ...)

	return 1;
} ## end sub check_func_removes

# ------------------------------------------------------------------------
# --- Check for empty masks. These are blocks where the masked sources ---
# --- are gone. If there is an #else block, it will become and insert  ---
# --- block. If anything got changed, a message is left as a comment:  ---
# --- /// elogind empty mask removed            or                     ---
# --- /// elogind empty mask else converted                            ---
# ------------------------------------------------------------------------
sub check_empty_masks {

	# early exits:
	defined($hHunk)  or return 1;
	$hHunk->{useful} or return 1;

	log_debug("Checking empty mask removals ...");

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
	my $mask_message = "";

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# entering an elogind mask
		# ---------------------------------------
		if ( is_mask_start($$line) ) {

			# No checks needed, check_masks() already did that, and later pruning might make
			# checks here fail, if large else block removals got reverted and the hunk(s) pruned.
			$local_iib = 0;
			$local_imb = 1;

			$mask_block_start = $i;

			# Note down mask message in case we leave a message
			$$line =~ m,///\s*(.+)\s*$, and $mask_message = $1;

			next;
		} ## end if ( is_mask_start($$line...))

		# entering an elogind insert
		# ---------------------------------------
		if ( is_insert_start($$line) ) {
			$local_iib = 1;
			$local_ieb = 0;

			# Note down mask message in case we leave a message
			$$line =~ m,///\s*(.+)\s*$, and $mask_message = $1;

			next;
		} ## end if ( is_insert_start($$line...))

		# Count regular #if
		$$line =~ m/^-[${HASH}]if/msx and ++$regular_ifs;

		# Switching from Mask to else.
		# Note: Inserts have no #else, they make no sense.
		# ---------------------------------------
		if ( is_mask_else($$line) ) {
			$local_ieb = 1;

			# If the else starts right after a mask start, we have to do something about it, if there is enough space left in the patch
			# (Which should be the case as the else block would have lengthened it. But better check it to be safe!)
			if ( $i && ( $i == ( $mask_block_start + 1 ) ) && ( $i < ( $hHunk->{count} - 2 ) ) ) {

				# Re-enable the removal of the "#if 0" and of the "#else" line
				substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = "-";
				substr( $hHunk->{lines}[$i],       0, 1 ) = "-";

				# Add a note that we converted this and add an insert mask
				splice( @{ $hHunk->{lines} }, $i + 1, 0, ( "+/// elogind empty mask else converted", "+#if 1 /// $mask_message" ) );

				$hHunk->{count} += 2;
				$need_endif_conversion = 1;
				$i += 2;  ## Already known...
			} ## end if ( $i && ( $i == ( $mask_block_start...)))

			$mask_block_start = -1;

			next;
		} ## end if ( is_mask_else($$line...))

		# ending a Mask block
		# ---------------------------------------
		if ( is_mask_end($$line) ) {

			# If the endif is right after the mask start, we have to do something about it, but only if we have enough space left in the patch
			if ( $i < ( $hHunk->{count} - 2 ) ) {
				if ( $i && ( $i == ( $mask_block_start + 1 ) ) ) {

					# Re-enable the removal of the "#if 0" and of the "#endif" line
					substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = "-";
					substr( $hHunk->{lines}[$i],       0, 1 ) = "-";

					# Add a note that we converted this
					splice( @{ $hHunk->{lines} },
						$i + 1, 0, ( '+' . ( $hFile{is_sh} ? '# ' : '' ) . "/// elogind empty mask removed ($mask_message)" ) );

					$hHunk->{count} += 1;
				} ## end if ( $i && ( $i == ( $mask_block_start...)))

				# If we need an endif conversion, do it now:
				elsif ( $need_endif_conversion > 0 ) {

					# First re-enable the removal:
					substr( $hHunk->{lines}[$i], 0, 1 ) = "-";

					# Add the correct endif
					splice( @{ $hHunk->{lines} }, $i + 1, 0, ("+#endif // 1") );

					$hHunk->{count} += 1;
					$i += 1;               ## Already known...
				} ## end elsif ( $need_endif_conversion...)
			} ## end if ( $i < ( $hHunk->{count...}))

			$local_imb             = 0;
			$local_ieb             = 0;
			$mask_block_start      = -1;
			$mask_message          = "";
			$need_endif_conversion = 0;

			next;
		} ## end if ( is_mask_end($$line...))

		# ending an insert block
		# ---------------------------------------
		if ( is_insert_end($$line) ) {
			$local_iib             = 0;
			$local_ieb             = 0;
			$mask_block_start      = -1;
			$mask_message          = "";
			$need_endif_conversion = 0;

			next;
		} ## end if ( is_insert_end($$line...))

		# end regular #if
		$$line =~ m/^-[${HASH}]endif/msx and --$regular_ifs;

	} ## end for ( my $i = 0 ; $i < ...)

	return 1;
} ## end sub check_empty_masks

# -----------------------------------------------------------------------
# --- Check hunk for include manipulations we must step in            ---
# --- This is basically read_include(), but this time we actually act ---
# --- on what we found.                                               ---
# --- Rules:                                                          ---
# --- 1) Removals of includes that we commented out:                  ---
# ---    a) If there is no insertion of this include, let it be       ---
# ---       removed, it seems to be obsolete.                         ---
# ---    b) If there is an insertion of the very same include in one  ---
# ---       of the surrounding lines, mark the insert for splicing    ---
# ---       and undo the removal.                                     ---
# --- 2) Insertions of new includes, where 1) does not apply:         ---
# ---    a) If the include is new, let its be added. (*)              ---
# ---    b) If the include is part of the "needed by elogind" block   ---
# ---       already, allow the removal there and accept the regular   ---
# ---       insertion here.                                           ---
# --- 3) Removals of includes in "needed by elogind" blocks:          ---
# ---    As 1) and 2) do not apply, simply undo any removal here.     ---
# --- (*) : We used to comment out new includes for later checks. But ---
# ---       big updates became an unbearable workload like that. Do a ---
# ---       cleanup of the includes later seems to be the better way. ---
# -----------------------------------------------------------------------
sub check_includes {

	# early exits:
	defined($hHunk)  or return 1;
	$hHunk->{useful} or return 1;

	log_debug("Checking includes ...");

	# We must know when "needed by elogind blocks" start
	my $in_elogind_block = 0;

	# The simple undo check will fail, if we do at least one at once.
	# Delay the undoing of the removals until after the hunk was checked.
	my %undos = ();

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# === Ruleset 1 : Handling of removals of includes we commented out ===
		# =====================================================================
		if ( $$line =~ m/^[${DASH}]\s*\/[\/*]+\s*[${HASH}]include\s+[<"']([^>"']+)[>"']\s*(?:\*\/)?/msx ) {
			$hIncs{$1}{applied} and next;  ## No double handling

			my $inc = $1;

			# Pre: Sanity check:
			defined( $hIncs{$inc}{remove}{hunkid} ) and $hIncs{$inc}{remove}{hunkid} > -1
			        or return hunk_failed("check_includes: Unrecorded removal found!");

			# a) Check for removals of obsolete includes.
			$hIncs{$inc}{elogind}{hunkid} > -1            ## If no insert was found, then the include was
			        or $hIncs{$inc}{insert}{hunkid} > -1  ## removed by systemd devs for good.
			        or ( ++$hIncs{$inc}{applied} and next );

			# b) Check for a simple undo of our commenting out
			if (       ( $hIncs{$inc}{insert}{hunkid} == $hIncs{$inc}{remove}{hunkid} )
				&& ( $hIncs{$inc}{insert}{sysinc} == $hIncs{$inc}{remove}{sysinc} ) )
			{
				my $ins_diff  = $hIncs{$inc}{insert}{lineid} - $hIncs{$inc}{remove}{lineid};
				my $all_same  = 1;
				my $direction = $ins_diff > 0 ? 1 : -1;

				# Let's see whether there are undos between this and its addition
				# in the same order, meaning there has been no resorting.
				for ( my $j = $direction ; ( $all_same > 0 ) && ( abs($j) < abs($ins_diff) ) ; $j += $direction ) {
					$all_same = 0;

					if (       ( $hHunk->{lines}[ $i + $j ] =~ m/^[${DASH}]\s*\/[\/*]+\s*[${HASH}]include\s+[<"']([^>"']+)[>"']\s*(?:\*\/)?/msx )
						|| ( $hHunk->{lines}[ $i + $j ] =~ m/^[${PLUS}]\s*[${HASH}]include\s+[<"']([^>"']+)[>"']/msx ) )
					{

						            $hIncs{$1}{insert}{hunkid} == $hIncs{$1}{remove}{hunkid}
						        and $ins_diff == ( $hIncs{$1}{insert}{lineid} - $hIncs{$1}{remove}{lineid} )
						        and $hIncs{$inc}{insert}{sysinc} == $hIncs{$inc}{remove}{sysinc}
						        and $all_same = 1;
					} ## end if ( ( $hHunk->{lines}...))
				} ## end for ( my $j = $direction...)
				if ( $all_same > 0 ) {

					# The insertion is right before or after the removal. That's pointless.
					$undos{ $hIncs{$inc}{remove}{lineid} } = 1;
					$hIncs{$inc}{applied}                  = 1;
					$hIncs{$inc}{insert}{spliceme}         = 1;
					next;
				} ## end if ( $all_same > 0 )
			} ## end if ( ( $hIncs{$inc}{insert...}))

			# c) Move somewhere else, or change include type. Can't be anything else here.
			if ( $hIncs{$inc}{elogind}{hunkid} > -1 ) {

				# Just undo the removal of the elogind insert.
				my $hId = $hIncs{$inc}{elogind}{hunkid};
				my $lId = $hIncs{$inc}{elogind}{lineid};
				substr( $hFile{hunks}[$hId]{lines}[$lId], 0, 1 ) = " ";
			} elsif ( $hIncs{$inc}{insert}{elogind} ) {

				# Do not move masked includes under our block.
				$undos{ $hIncs{$inc}{remove}{lineid} } = 1;
				$hIncs{$inc}{insert}{spliceme} = 1;
			} ## end elsif ( $hIncs{$inc}{insert...})

			$hIncs{$inc}{applied} = 1;
			next;
		} ## end if ( $$line =~ m/^[${DASH}]\s*\/[\/*]+\s*[${HASH}]include\s+[<"']([^>"']+)[>"']\s*(?:\*\/)?/msx)

		# === Ruleset 2 : Handling of insertions, not handled by 1          ===
		# =====================================================================
		if ( $$line =~ m/^[${PLUS}]\s*[${HASH}]include\s+[<"']([^>"']+)[>"']/msx ) {
			$hIncs{$1}{applied} and next;  ## No double handling

			# Pre: Sanity check:
			defined( $hIncs{$1}{insert}{hunkid} ) and $hIncs{$1}{insert}{hunkid} > -1
			        or return hunk_failed("check_includes: Unrecorded insertion found!");

			# Nicely enough we are already set here.
			$hIncs{$1}{applied} = 1;

			next;
		} ## end if ( $$line =~ m/^[${PLUS}]\s*[${HASH}]include\s+[<"']([^>"']+)[>"']/msx)

		# === Ruleset 3 : Handling of "needed by elogind" blocks            ===
		# =====================================================================
		if ( $in_elogind_block
			&& ( $$line =~ m/^[${DASH}]\s*[${HASH}]include\s+[<"']([^>"']+)[>"']/msx ) )
		{
			$hIncs{$1}{applied} and next;  ## No double handling

			# Pre: Sanity check:
			defined( $hIncs{$1}{elogind}{hunkid} ) and $hIncs{$1}{elogind}{hunkid} > -1
			        or return hunk_failed("check_includes: Unrecorded elogind include found!");

			# As 1 and 2 do not apply, simply undo the removal.
			substr( $$line, 0, 1 ) = " ";
			$hIncs{$1}{applied} = 1;

			next;
		} ## end if ( $in_elogind_block...)

		# === Other 1 : Look for "needed by elogind" block starts           ===
		# =====================================================================
		if ( $$line =~ m/^[- ]\s*\/\/+.*needed\s+(?:by|for)\s+elogind.*/misx ) {
			$in_elogind_block = 1;

			# Never remove the block start
			( $$line =~ m,^[${DASH}], ) and substr( $$line, 0, 1 ) = " ";

			# While we are here, we can see to it, that the additional empty
			# line above our marker does not get removed:
			( $i > 0 )
			        and ( $hHunk->{lines}[ $i - 1 ] =~ m/^-\s*$/ )
			        and substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = " ";

			next;
		} ## end if ( $$line =~ m/^[- ]\s*\/\/+.*needed\s+(?:by|for)\s+elogind.*/misx)

		# === Other 2 : elogind include blocks end, when the first line is  ===
		# ===           found that does not starts with #include            ===
		# ===
		# =====================================================================
		if ( $in_elogind_block && !( $$line =~ m/^.\s*[${HASH}]include$/msx ) ) {

			# diff may want to remove the first empty line after our block.
			( $$line =~ m,^[${DASH}]\s*$, ) and substr( $$line, 0, 1 ) = " ";

			# Done now...
			$in_elogind_block = 0;
		} ## end if ( $in_elogind_block...)

		# === Other 3 : Undo all other removals in elogind include blocks   ===
		# =====================================================================
		$in_elogind_block and ( $$line =~ m,^[${DASH}], ) and substr( $$line, 0, 1 ) = " ";

		# Note: Although it looks like all rules are out the window here, all
		#       elogind includes that are handled above, end in a 'next', so
		#       those won't reach here. Actually 'Other 3' would be never
		#       reached with an #include line.

	} ## end for ( my $i = 0 ; $i < ...)

	# Before we can leave, we have to neutralize the %undo lines:
	for my $lId ( keys %undos ) {
		substr( $hHunk->{lines}[$lId], 0, 1 ) = " ";
	}

	return 1;
} ## end sub check_includes

sub check_logger {
	my ($logger) = @_;
	if ( defined $logger ) {
		$logger =~ m/^log_(info|warning|error|status|debug|change)$/xms
		        or confess("logMsg() called from wrong sub $logger");
	}
	return 1;
} ## end sub check_logger

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
sub check_masks {

	# early exits:
	defined($hHunk)  or croak("check_masks: hHunk is undef");
	$hHunk->{useful} or croak("check_masks: Nothing done but hHunk is useless?");

	log_debug("Checking mask flips ...");

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

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# entering an elogind mask
		# ---------------------------------------
		if ( is_mask_start($$line) ) {
			$in_mask_block and return hunk_failed("check_masks: Mask start found while being in a mask block!");
			$in_insert_block
			        and return hunk_failed("check_masks: Mask start found while being in an insert block!");
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_insert_block  = 0;
			$in_mask_block    = 1;
			$mask_block_start = $i;
			$mask_end_line    = -1;
			$move_to_line     = -1;

			# While we are here we can check the previous line.
			# All masks shall be preceded by an empty line to enhance readability.
			# So any attempt to remove them must be stopped.
			( $i > 0 )
			        and ( $hHunk->{lines}[ $i - 1 ] =~ m/^-\s*$/ )
			        and substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = " ";

			next;
		} ## end if ( is_mask_start($$line...))

		# entering an elogind insert
		# ---------------------------------------
		if ( is_insert_start($$line) ) {
			$in_mask_block   and return hunk_failed("check_masks: Insert start found while being in a mask block!");
			$in_insert_block and return hunk_failed("check_masks: Insert start found while being in an insert block!");
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_insert_block  = 1;
			$in_mask_block    = 0;
			$mask_block_start = -1;
			$mask_end_line    = -1;
			$move_to_line     = $i;

			# While we are here we can check the previous line.
			# All inserts shall be preceded by an empty line to enhance readability.
			# So any attempt to remove them must be stopped.
			( $i > 0 )
			        and ( $hHunk->{lines}[ $i - 1 ] =~ m/^-\s*$/ )
			        and substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = " ";

			next;
		} ## end if ( is_insert_start($$line...))

		# Count regular #if
		$$line =~ m/^-[${HASH}]if/msx and ++$regular_ifs;

		# Switching from Mask to else.
		# Note: Inserts have no #else, they make no sense.
		# ---------------------------------------
		if ( is_mask_else($$line) ) {
			$in_mask_block
			        or return hunk_failed("check_masks: Mask else found outside any mask block!");

			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_else_block = 1;
			$move_to_line  = $i;
			next;
		} ## end if ( is_mask_else($$line...))

		# ending a Mask block
		# ---------------------------------------
		if ( is_mask_end($$line) ) {
			$in_mask_block or return hunk_failed("check_masks: #endif // 0 found outside any mask block");
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_mask_block    = 0;
			$in_else_block    = 0;
			$mask_block_start = -1;
			$mask_end_line    = $i;
			next;
		} ## end if ( is_mask_end($$line...))

		# ending an insert block
		# ---------------------------------------
		if ( is_insert_end($$line) ) {
			$in_insert_block or return hunk_failed("check_masks: #endif // 1 found outside any insert block");
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_insert_block  = 0;
			$mask_block_start = -1;
			$mask_end_line    = $i;
			next;
		} ## end if ( is_insert_end($$line...))

		# end regular #if
		$$line =~ m/^-[${HASH}]endif/msx and --$regular_ifs;

		# Special treatment for all mask-else and insert blocks.
		# (Well, that's what this function is all about, isn't it?)
		if ( $in_insert_block || ( $in_mask_block && $in_else_block ) ) {

			# Remove '-' prefixes in all lines within insert and mask-else blocks
			# -------------------------------------------------------------------
			if ( $$line =~ m,^[${DASH}], ) {
				substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			}

			# Special check for additions/keepers that might (will!) wreak havoc:
			# -------------------------------------------------------------------
			elsif ( $move_to_line > -1 ) {

				# The following cases have been met:
				# a) upstream adds something after a mask #else block ( See issues #1 and #4 )
				# b) name reverts push lines under a mask start
				# c) diff removes lines from a masked block or before an insert, but keeps
				#    common lines inside mask-else or insert blocks
				# d) as a follow-up on c), diff wants to add a line and adds it after the
				#    kept common line inside our domain.
				# All these cases can be handled with two simple solutions.
				# ------------------------------------------------------------------------------------
				my $cpy_line = $$line;

				# Case 1 ; The keeper: Copy the offending line back above the else/insert
				# -----------------------------------------------------------------------
				if ( $$line =~ m,^ , ) {
					substr( $cpy_line, 0, 1 ) = "+";  ## Above, this is an addition.
					splice( @{ $hHunk->{lines} }, $move_to_line++, 0, $cpy_line );
					$hHunk->{count} += 1;
					$i++;                             ## We have to advance i, or the next iteration puts as back here.
				} ## end if ( $$line =~ m,^ , )

				# Case 2 ; The addition: move the offending line back above the else/insert
				# -----------------------------------------------------------------------
				else {
					splice( @{ $hHunk->{lines} }, $i, 1 );  ## Order matters here.
					splice( @{ $hHunk->{lines} }, $move_to_line++, 0, $cpy_line );

					# Note: No change to $hHunk->{count} here, as the lines are moved.
				} ## end else [ if ( $$line =~ m,^ , )]

				# No matter whether we have copied or moved, the if/else moved down.
				$mask_end_line > -1 and ++$mask_end_line or ++$mask_block_start;

				next;
			} ## end elsif ( $move_to_line > -1)
		} ## end if ( $in_insert_block ...)

		# Being here means that we are in a mask block or outside of any block.
		# A special thing to consider is when diff wants to change the end or
		# add something to the end of a mask block, or right before an insertion
		# block.
		# As our blocks are getting removed by diff, the addition will happen
		# right after that. So anything added the very next lines after we have
		# exited our domain must be moved up.
		if ( 0 == $in_mask_block ) {
			if ( ( $move_to_line > -1 ) && ( $$line =~ m,^[${PLUS}], ) ) {
				my $cpy_line = $$line;
				splice( @{ $hHunk->{lines} }, $i, 1 );  ## Order matters here.
				splice( @{ $hHunk->{lines} }, $move_to_line++, 0, $cpy_line );

				# Note: Again no change to $hHunk->{count} here, as the lines are moved.
				next;
			} ## end if ( ( $move_to_line >...))

			# end our mask block ending awareness at the first non-insertion line after a mask block.
			# ---------------------------------------------------------------------------------------
			$mask_end_line = -1;
			$move_to_line  = -1;
		} ## end if ( 0 == $in_mask_block)
	} ## end for ( my $i = 0 ; $i < ...)

	# Note down how this hunk ends before first pruning
	$hHunk->{masked_end} = $in_mask_block && !$in_else_block ? 1 : 0;

	return 1;
} ## end sub check_masks

# -----------------------------------------------------------------------
# --- Check for musl_libc compatibility blocks                        ---
# --- Rules:                                                          ---
# --- For musl-libc compatibility, there are some                     ---
# ---   #ifdef __GLIBC__ (...) #else (...) #endif // __GLIBC__        ---
# --- helpers.                                                        ---
# --- These can also be "#if defined(__GLIBC__)"                      ---
# --- Note: We handle them like regular mask blocks, because the      ---
# ---       __GLIBC__ block is considered to be the original, while   ---
# ---       the musl_libc compat block is the #else block.            ---
# -----------------------------------------------------------------------
sub check_musl {

	# early exits:
	defined($hHunk)  or return 0;
	$hHunk->{useful} or return 0;

	log_debug("Checking musl libc protection ...");

	# Count non-elogind block #ifs. This is needed, so normal
	# #if/#else/#/endif constructs can be put inside both the original
	# and the alternative block.
	my $regular_ifs = 0;

	# Remember the final mask state for later reversal
	# ------------------------------------------------
	my $hunk_ends_in_mask = $in_mask_block;
	my $hunk_ends_in_else = $in_else_block;
	$in_else_block = 0;
	$hHunk->{masked_start} and $in_mask_block = 1 or $in_mask_block = 0;

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# The increment/decrement variant can cause negative values:
		$in_mask_block < 0 and $in_mask_block = 0;
		$in_else_block < 0 and $in_else_block = 0;

		# Quick mask checks, we must have the intermediate states
		# -------------------------------------------------------
		is_mask_start($$line) and ++$in_mask_block and next;
		if ( is_mask_end($$line) ) {
			$in_mask_block--;
			$in_else_block--;
			next;
		}

		# entering a __GLIBC__ block as mask
		# ---------------------------------------
		if ( $$line =~ m/^-[${HASH}]if(?:def|\s+defined).+__GLIBC__/msx ) {
			## Note: Here it is perfectly fine to be in an elogind mask block.
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_glibc_block = 1;
			next;
		} ## end if ( $$line =~ m/^-[${HASH}]if(?:def|\s+defined).+__GLIBC__/msx)

		# entering a __GLIBC__ block as insert
		# ---------------------------------------
		if ( $$line =~ m/^-[${HASH}]if(?:ndef|\s+!defined).+__GLIBC__/msx ) {
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_glibc_block = 1;
			$in_else_block++;
			next;
		} ## end if ( $$line =~ m/^-[${HASH}]if(?:ndef|\s+!defined).+__GLIBC__/msx)

		# Count regular #if
		$$line =~ m/^-[${HASH}]if/msx and ++$regular_ifs;

		# Switching from __GLIBC__ to else
		# ---------------------------------------
		if ( $$line =~ m/^[-${SPACE}]?[${HASH}]else\s+[\/]+\s+__GLIBC__/msx ) {
			++$in_else_block;
			substr( $$line, 0, 1 ) = " ";
			next;
		}

		# ending a __GLBC__ block
		# ---------------------------------------
		if ( $$line =~ m/^[${DASH}][${HASH}]endif\s*\/\/\/?.*__GLIBC__/msx ) {
			( !$in_glibc_block )
			        and return hunk_failed("check_musl: #endif // __GLIBC__ found outside any __GLIBC__ block");
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
			$in_glibc_block = 0;
			$in_else_block--;
			next;
		} ## end if ( $$line =~ m/^[${DASH}][${HASH}]endif\s*\/\/\/?.*__GLIBC__/msx)

		# end regular #if
		$$line =~ m/^-[${HASH}]endif/msx and --$regular_ifs;

		# Remove '-' prefixes in all lines within the musl (#else) blocks
		# -------------------------------------------------------------------
		if (       ( $$line =~ m,^[${DASH}], )
			&& ( $in_glibc_block > 0 )
			&& ( $in_else_block > $in_mask_block ) )
		{
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'
		} ## end if ( ( $$line =~ m,^[${DASH}],...))
	} ## end for ( my $i = 0 ; $i < ...)

	# Revert the final mask state remembered above
	# ------------------------------------------------
	$in_mask_block = $hunk_ends_in_mask;
	$in_else_block = $hunk_ends_in_else;

	return 1;
} ## end sub check_musl

# -----------------------------------------------------------------------
# --- Check for attempts to revert 'elogind' to 'systemd'             ---
# -----------------------------------------------------------------------
sub check_name_reverts {

	# early exits:
	defined($hHunk)  or return 0;
	$hHunk->{useful} or return 0;

	log_debug("Checking name reversals elogind->systemd ...");

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
	# ------------------------------------------------
	my $hunk_ends_in_mask = $in_mask_block;
	my $hunk_ends_in_else = $in_else_block;
	$hHunk->{masked_start} and $in_mask_block = 1 or $in_mask_block = 0;

	# The increment/decrement variant can cause negative values
	$in_mask_block < 0 and $in_mask_block = 0;
	$in_else_block = 0;

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line_p = \$hHunk->{lines}[$i];  ## Shortcut
		defined($$line_p)
		        or return hunk_failed( "check_name_reverts: Line " . ( $i + 1 ) . "/$hHunk->{count} is undef?" );

		# Quick mask checks, we must have the intermediate states
		# -------------------------------------------------------
		is_mask_start($$line_p) and ++$in_mask_block and next;
		is_mask_else($$line_p)  and ++$in_else_block and next;
		if ( is_mask_end($$line_p) ) {
			$in_mask_block = 0;
			$in_else_block = 0;
			next;
		}
		my $is_masked_now = ( ( 0 < $in_mask_block ) && ( 1 > $in_else_block ) ) ? 1 : 0;

		# Analyze basic status of the line
		# -----------------------------------------------------------
		change_analyze_hunk_line( \%hChanges, $i, $$line_p, $is_masked_now );
	} ## end for ( my $i = 0 ; $i < ...)

	# Generally there are three types of changes:
	# 1) The simple removal, when there is only one change of type -1
	# 2) The simple addition, when there is only one change of type +1
	# 3) The change where there is an even number of changes with two consecutive being type opposites
	#    ( This can be an addition followed by a removal or a removal followed by an addition. )
	# However, we have to find the counterpart to the change before we can do anything, and for
	# that to work all changes of the hunk have to be recorded first.
	change_map_hunk_lines( \%hChanges );

	# Before we can process our findings, we have to protect false positives, like mentioning of systemd daemons elogind does not ship.
	change_handle_false_positives( \%hChanges );

	# Before we can go through our findings, we have to check the solos, meaning additions and removals that have no partner set.
	# Removals are okay, unless they contain an elogind function call.
	# Additions have to be checked for possible systemd->elogind renaming
	change_check_solo_changes( \%hChanges );

	# Check additions that have not been handled with.
	change_handle_additions( \%hChanges );

	# Upward removals (where the addition comes first) are handled with last
	change_handle_removals( \%hChanges );

	# Splice the lines that were noted for splicing
	# ------------------------------------------------
	change_splice_the_undone( \%hChanges );

	# Revert the final mask state remembered above
	# ------------------------------------------------
	$in_mask_block = $hunk_ends_in_mask;
	$in_else_block = $hunk_ends_in_else;

	return 1;
} ## end sub check_name_reverts

# -----------------------------------------------------------------------
# --- Check for __STDC_VERSION__ guards                               ---
# --- Rules:                                                          ---
# ---   In some headers __STDC_VERSION__ is used unconditionally.     ---
# ---   This causes trouble in C++ builds, as that macro is not set   ---
# ---   there. In elogind this macro is always guarded.               ---
# -----------------------------------------------------------------------
sub check_stdc_version {

	# early exits:
	defined($hHunk)  or return 0;
	$hHunk->{useful} or return 0;

	log_debug("Checking __STDC_VERSION__ guards...");

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
	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# The increment/decrement variant can cause negative values:
		$in_mask_block < 0 and $in_mask_block = 0;
		$in_else_block < 0 and $in_else_block = 0;

		# Quick mask checks, we must have the intermediate states
		# -------------------------------------------------------
		is_mask_start($$line) and ++$in_mask_block and next;
		if ( is_mask_end($$line) ) {
			$in_mask_block--;
			$in_else_block--;
			next;
		}

		# Having a removal of a guardian
		# ---------------------------------------
		if ( $$line =~ m/^[${DASH}][${HASH}]\s*if\s+defined\(__STDC_VERSION__\)\s+&&\s+/msx ) {
			## Note: Here it is perfectly fine to be in an elogind mask block.
			$line_del_num = $i;
			$line_del_str = $$line;
			next;
		} ## end if ( $$line =~ m/^[${DASH}][${HASH}]\s*if\s+defined\(__STDC_VERSION__\)\s+&&\s+/msx)

		# Having the line without guardian added
		# ---------------------------------------
		if ( $$line =~ m/^[${PLUS}][${HASH}]\s*if\s+/msx ) {
			$line_rep_num = $i;
			$line_rep_str = $$line;
		}

		# If we have a deletion and a fitting addition in the next line,
		# revert the first and remove the second.
		if ( ( $line_del_num > -1 ) && ( ( $line_del_num + 1 ) == $line_rep_num ) && ( $line_rep_str =~ /^[${PLUS}][${HASH}](\s*)if\s+(\S.*)$/msx ) ) {
			my $alt_line = "-#${1}if defined(__STDC_VERSION__) && $2";
			if ( $alt_line eq $line_del_str ) {

				# Yes, the just want to take out the guard.
				# Let's revert that
				substr( $hHunk->{lines}[$line_del_num], 0, 1 ) = " ";
				splice( @{ $hHunk->{lines} }, $line_rep_num, 1 );
				--$hHunk->{count};
			} ## end if ( $alt_line eq $line_del_str)
			$line_del_num = -1;
			$line_rep_num = -1;
		} ## end if ( ( $line_del_num >...))
	} ## end for ( my $i = 0 ; $i < ...)

	# Revert the final mask state remembered above
	# ------------------------------------------------
	$in_mask_block = $hunk_ends_in_mask;
	$in_else_block = $hunk_ends_in_else;

	return 1;
} ## end sub check_stdc_version

# -----------------------------------------------------------------------
# --- Check for attempts to uncomment unsupported API functions       ---
# --- in .sym files.                                                  ---
# --- In here we change unsupported function calls from               ---
# ---        sd_foo_func;                                             ---
# --- to                                                              ---
# ---        /* sd_foo_func; */                                       ---
# -----------------------------------------------------------------------
sub check_sym_lines {

	# early exits:
	defined($hHunk)  or return 0;
	$hHunk->{useful} or return 0;

	# Only .sym files are handled here
	$hFile{source} =~ m/\.sym\.pwx$/ or return 1;

	log_debug("Checking .sym file sanity...");

	# Note down what is changed, so we can have inline updates
	my %hAdditions = ();
	my %hRemovals  = ();

	# We need a sortable line map for possible later splicing
	my %hAddMap = ();

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		defined($$line)
		        or return hunk_failed( "check_sym_files: Line " . ( $i + 1 ) . "/$hHunk->{count} is undef?" );

		# Note down removals
		# ---------------------------------
		if ( $$line =~ m/^[${DASH}]\s*\/\*\s+(\S.+;)\s+\*\/\s*$/msx ) {
			$hRemovals{$1}{line} = $i;
			next;
		}

		# Check Additions
		# ---------------------------------
		if ( $$line =~ m/^[${PLUS}]\s*([^${SPACE}\/].+;)\s*$/msx ) {
			$hAdditions{$1}{line}    = $i;
			$hAdditions{$1}{handled} = 0;
			$hAddMap{$i}             = $1;
		}
	} ## end for ( my $i = 0 ; $i < ...)

	# Now we go backwards through the lines that got added and revert the reversals.
	for my $i ( sort { $b <=> $a } keys %hAddMap ) {
		my $item = $hAddMap{$i};

		# First a sanity check against double insertions.
		$hAdditions{$item}{handled}
		        and return hunk_failed( "check_sym_files: Line" . ( $i + 1 ) . ": Double addition of \"$item\" found!" );

		# New stuff is in order:
		defined( $hRemovals{$item} ) or ++$hAdditions{$item}{handled} and next;

		# Here we simply undo the removal and splice the addition:
		substr( $hHunk->{lines}[ $hRemovals{$item}{line} ], 0, 1 ) = " ";
		splice( @{ $hHunk->{lines} }, $i, 1 );
		$hAdditions{$item}{handled} = 1;
		--$hHunk->{count};
	} ## end for my $i ( sort { $b <=>...})

	return 1;
} ## end sub check_sym_lines

# -----------------------------------------------------------------------
# --- Check for useless updates that do nothing.                      ---
# --- The other checks and updates can lead to hunks that effectively ---
# --- do nothing as they end up like:                                 ---
# --- -foo                                                            ---
# --- -bar                                                            ---
# --- +foo                                                            ---
# --- +bar                                                            ---
# -----------------------------------------------------------------------
sub check_useless {

	# early exits:
	defined($hHunk)  or croak("check_useless: hHunk is undef");
	$hHunk->{useful} or croak("check_useless: Nothing done but hHunk is useless?");

	log_debug("Checking for useless updates...");

	# Note down removals, and where they start
	my %hRemovals = ();
	my $r_start   = -1;

	# We later work with an offset, to check for useless changes to splice
	my %hSplices = ();
	my $r_offset = -1;

	# Now go through the line and find out what is to be done
	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# --- (1) Note down removal ---
		if ( $$line =~ m/^-(.*)$/ ) {
			my $token = $1 || "";
			$token =~ s/\s+$//;       ## No trailing whitespace/lines!
			$r_start > -1 or $r_start = $i;
			length($token) and $hRemovals{$token} = $i
			        or $hRemovals{ "empty" . $i } = $i;
			next;
		} ## end if ( $$line =~ m/^-(.*)$/)

		# --- (2) Check Addition ---
		if ( $$line =~ m/^[${PLUS}](.*)$/ ) {
			my $token = $1 || "";
			$token =~ s/\s+$//;       ## No trailing whitespace/lines!
			$r_offset > -1 or $r_offset = $i - $r_start;
			if (       ( length($token) && ( defined( $hRemovals{$token} ) && ( $hRemovals{$token} + $r_offset ) == $i ) )
				|| ( !length($token) && ( defined( $hRemovals{ "empty" . ( $i - $r_offset ) } ) ) ) )
			{
				# Yep, this has to be reverted.
				substr( $hHunk->{lines}[ $i - $r_offset ], 0, 1 ) = " ";
				$hSplices{$i} = 1;
			} ## end if ( ( length($token) ...))
			next;
		} ## end if ( $$line =~ m/^[${PLUS}](.*)$/)

		# --- (3) Reset state on the first out-of-block line
		$r_start   = -1;
		$r_offset  = -1;
		%hRemovals = ();
	} ## end for ( my $i = 0 ; $i < ...)

	# Now go through the splice map and splice from back to front
	for my $line_no ( sort { $b <=> $a } keys %hSplices ) {
		log_debug( "  => Splicing Line %d: \"%s\"", $line_no, $hHunk->{lines}[$line_no] );
		splice( @{ $hHunk->{lines} }, $line_no, 1 );
		$hHunk->{count}--;
	}

	return 1;
} ## end sub check_useless

# -----------------------------------------------------------------------
# --- Checkout the given refid on $upstream_path                      ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub checkout_upstream {
	my ($commit) = @_;

	# It is completely in order to not wanting to checkout a specific commit.
	defined($commit) and length($commit) or return 1;

	my $new_commit = "";
	my $git        = Git::Wrapper->new($upstream_path);
	my @lOut       = ();

	# Save the previous commit
	try {
		@lOut = $git->rev_parse( { short => 1 }, "HEAD" );
	} catch {
		log_error( "Couldn't rev-parse $upstream_path HEAD\nExit Code : %s\nMessage   : %s", $_->status, $_->error );
		return 0;
	};
	$previous_commit = $lOut[0];

	# Get the shortened commit hash of $commit
	try {
		@lOut = $git->rev_parse( { short => 1 }, $commit );
	} catch {
		log_error( "Couldn't rev-parse %s \"%s\"\nExit Code : %s\nMessage   : %s", $upstream_path, $commit, $_->status, $_->error );
		return 0;
	};
	$new_commit = $lOut[0];

	# Now check it out, unless we are already there:
	if ( $previous_commit ne $new_commit ) {
		show_progress( 0, "Checking out %s in upstream tree...", $new_commit );
		try {
			$git->checkout($new_commit);
		} catch {
			log_error( "Couldn't checkout \"%s\" in %s\nExit Code : %s\nMessage   : %s", $new_commit, $upstream_path, $_->status, $_->error );
			return 0;
		};
		show_progress( 1, "Checking out %s in upstream tree... done!", $new_commit );
	} ## end if ( $previous_commit ...)

	return 1;
} ## end sub checkout_upstream

# -----------------------------------------------------------------------
# --- Completely clean up the current %hFile data structure.          ---
# -----------------------------------------------------------------------
sub clean_hFile {
	defined( $hFile{count} ) or return 1;

	for ( my $i = $hFile{count} - 1 ; $i > -1 ; --$i ) {
		defined( $hFile{hunks}[$i] ) and undef( %{ $hFile{hunks}[$i] } );
	}

	$hFile{count}  = 0;
	$hFile{hunks}  = [];
	$hFile{output} = [];

	return 1;
} ## end sub clean_hFile

# A die handler that lets perl death notes be printed via log
sub dieHandler {
	my ($err) = @_;

	$death_note = 5;
	$ret_global = 42;

	log_error( '%s', $err );

	confess('Program died');
} ## end sub dieHandler

# -----------------------------------------------------------------------
# --- Builds the diff between source and target file, and stores all  ---
# --- hunks in $hFile{hunks} - if any.                                ---
# --- Returns 1 on success and 0 if the files are the same.           ---
# -----------------------------------------------------------------------
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
	@{ $hFile{output} } = splice( @lDiff, 0, 2 );
	chomp $hFile{output}[0];                            # These now have absolute paths, and source meson files have a
	chomp $hFile{output}[1];                            # .pwx extensions. That is not what the result shall look like.
	$hFile{create}                                      # But we have $hFile{part}, which is already the
	        and $hFile{output}[0] =~ s,$src,/dev/null,  # relative file name of the file we are
	        or $hFile{output}[0]  =~ s,$src,a/$prt,;    # processing, and we know if a file is
	$hFile{output}[1] =~ s,$tgt,b/$prt,;                # to be created.

	# ... and the raw hunks can be stored.
	for ( my $line_no = 1 ; $line_no < scalar @lDiff ; ++$line_no ) {
		( '@@' eq substr( $lDiff[$line_no], 0, 2 ) )
		        and ( build_hHunk( splice( @lDiff, 0, $line_no ) ) or return 0 )
		        and $line_no = 0;
	}
	scalar @lDiff and build_hHunk(@lDiff);

	return 1;
} ## end sub diff_hFile

sub do_prechecks {
	my $result = 1;

	# If --create was given, @wanted_files must not be empty
	if ( $result && !$show_help && $do_create && ( 0 == scalar @wanted_files ) ) {
		print "ERROR: --create must not be used on the full tree!\n";
		print "       Add at least one file using the --file option.\n";
		$result = 0;
	}

	# If --stay was given, $wanted_commit must not be empty
	if ( $result && !$show_help && $do_stay && ( 0 == length($wanted_commit) ) ) {
		print "ERROR: --stay makes only sense with the -c|--commit option!\n";
		$result = 0;
	}

	# If any of the wanted files do not exist, error out unless --create was used.
	if ( $result && !$show_help && defined( $wanted_files[0] ) ) {
		foreach my $f (@wanted_files) {
			-f $f
			        or $do_create and $hToCreate{$f} = 1
			        or print "ERROR: $f does not exist!\n" and $result = 0;
		}
	} ## end if ( $result && !$show_help...)

	return $result;
} ## end sub do_prechecks

sub format_caller {
	my ($caller) = @_;
	$caller =~ s/^.*::([^:]+)$/$1/xms;
	$caller =~ m/__ANON__/xmsi and $caller = 'AnonSub';
	return $caller;
} ## end sub format_caller

# -----------------------------------------------------------------------
# --- Finds all relevant files and store them in @wanted_files        ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub generate_file_list {

	# Do some cleanup first. Just to be sure.
	my $r;
	$r = qx{rm -rf build*};
	$r = qx{find -iname '*.orig' -or -iname '*.bak' -or -iname '*.rej' -or -iname '*~' -or -iname '*.gc??' | xargs rm -f};

	# Build wanted files hash
	while ( my $want = shift @wanted_files ) {
		$have_wanted              = 1;
		$want =~ m,^\./, or $want = "./$want";
		$hWanted{$want}           = 1;
		$want =~ s/elogind/systemd/msg;
		$hWanted{$want} = 1;
	} ## end while ( my $want = shift ...)

	# The idea now is, that we use File::Find to search for files
	# in all legal directories this program allows. Checking against
	# the built %hWanted ensures that a user provided list of files
	# is heeded.
	for my $xDir ( "doc", "docs", "factory", "m4", "man", "po", "shell-completion", "src", "tools" ) {
		if ( -d "$xDir" ) {
			find( \&wanted, "$xDir" );
		}
	}

	# There are a few root files we need to check, too
	for my $xFile ( "configure", "Makefile", "meson.build", "meson_options.txt" ) {
		if ( -f "$xFile" ) {
			find( \&wanted, "$xFile" );
		}
	}

	# If the user wants to check files, that do not show up when
	# searching our predefined set of directories, then let them.
	for my $xFile ( keys %hWanted ) {

		# Files with systemd<->elogind alternatives might not be there
		-f "$xFile" or $hWanted{$xFile} = 2;
		$hWanted{$xFile} == 2 and next;  ## Already handled or unavailable
		find( \&wanted, "$xFile" );
	} ## end for my $xFile ( keys %hWanted)

	# All files that shall be created must be added manually now.
	scalar keys %hToCreate and push @source_files, keys %hToCreate;

	# Just to be sure...
	scalar @source_files
	        or log_error("No source files found? Where the hell are we?")
	        and return 0;

	# Get the maximum file length and build $file_fmt
	my $mlen = 0;
	for my $f (@source_files) {
		length($f) > $mlen and $mlen = length($f);
	}
	$file_fmt = sprintf( "%%-%d%s", $mlen, "s" );

	return 1;
} ## end sub generate_file_list

# ------------------------------------------------------------------------
# --- Generate the "@@ -xx,n +yy,m @@" hunk header line out of $hHunk. ---
# --- Returns the generated string, with 0 values if $hHunk is undef.  ---
# --- IMPORTANT: This function does *NOT* prune $hHunk->{lines} !      ---
# ------------------------------------------------------------------------
sub get_hunk_head {
	my ($offset) = @_;

	my $src_len   = 0;
	my $tgt_len   = 0;
	my $lCount    = $hHunk->{count};
	my $src_start = $hHunk->{src_start};
	my $tgt_start = defined($offset) ? $src_start + $$offset : $hHunk->{tgt_start};

	for ( my $i = 0 ; $i < $lCount ; ++$i ) {
		if ( $hHunk->{lines}[$i] =~ m/^[${PLUS}]/ ) {
			$tgt_len++;
		} elsif ( $hHunk->{lines}[$i] =~ m/^\-/ ) {
			$src_len++;
		} else {
			$src_len++;
			$tgt_len++;
		}
	} ## end for ( my $i = 0 ; $i < ...)

	# If an offset reference was given, add back the size diff
	defined($offset)
	        and $$offset += $tgt_len - $src_len;

	return sprintf( "%s -%d,%d +%d,%d %s", '@@', $src_start, $src_len, $tgt_start, $tgt_len, '@@' );
} ## end sub get_hunk_head

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

# -----------------------------------------------------------------------
# --- Whenever a check finds an illegal situation, it has to call     ---
# --- this subroutine which terminates the progress line and creates  ---
# --- an entry in @lFails.                                            ---
# --- Param: An error message, preferably with the name of the failed ---
# ---        check.                                                   ---
# --- Return: Always zero.                                            ---
# -----------------------------------------------------------------------
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
	for my $line ( @{ $hHunk->{lines} } ) {
		push @{ $lFails[$num]{hunk} }, $line;
	}

	# And terminate the progress line:
	show_progress( 1, "$file_fmt : %s", $hFile{part}, $msg );

	return 0;
} ## end sub hunk_failed

# -----------------------------------------------------------------------
# --- Check the current $hHunk whether it still does anything.        ---
# --- While being at it, prune it to what a diff needs:               ---
# ---   3 lines before the first and 3 lines after the last change.   ---
# --- Returns 1 if at least one change was found, 0 otherwise.        ---
# -----------------------------------------------------------------------
sub hunk_is_useful() {

	# early exits:
	( $death_note > 0 ) and return 0;
	defined($hHunk)  or return 0;
	$hHunk->{useful} or return 0;

	log_debug("Checking whether the hunk is still useful ...");

	# Go through the lines and see whether we have any changes
	my $is_useful = 0;

	for ( my $i = 0 ; ( 0 == $is_useful ) && ( $i < $hHunk->{count} ) ; ++$i ) {
		if ( $hHunk->{lines}[$i] =~ m/^[-+]/ ) {
			$is_useful = 1;
		}
	}

	$hHunk->{useful} = $is_useful;
	log_debug( "  => Hunk is %s useful", ( $is_useful > 0 ) ? "still" : "no longer" );

	if ( ( $do_debug > 0 ) && ( $is_useful > 0 ) ) {
		for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
			log_info( "% 3d: %s", $i + 1, $hHunk->{lines}[$i] );
		}
	}

	return $is_useful;
} ## end sub hunk_is_useful

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any insertion end ---
# --------------------------------------------------------------
sub is_insert_end {
	my ($line) = @_;

	defined($line) and length($line) or return 0;

	if (       ( $line =~ m/^[-${SPACE}]?[${HASH}]endif\s*\/(?:[*\/]+)\s*1/msx )
		|| ( $line =~ m/\/\/\s+1\s+-->\s*$/msx )
		|| ( $line =~ m/\*\s+\/\/\s+1\s+\*\*\/\s*$/msx ) )
	{
		return 1;
	} ## end if ( ( $line =~ m/^[-${SPACE}]?[${HASH}]endif\s*\/(?:[*\/]+)\s*1/msx...))

	return 0;
} ## end sub is_insert_end

# ----------------------------------------------------------------
# --- Return 1 if the argument consists of any insertion start ---
# ----------------------------------------------------------------
sub is_insert_start {
	my ($line) = @_;

	defined($line) and length($line) or return 0;

	if (       ( $line =~ m/^[-${SPACE}]?[${HASH}]if\s+1.+elogind/msx )
		|| ( $line =~ m/<!--\s+1.+elogind.+-->\s*$/msx ) )
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

	defined($line) and length($line) or return 0;

	if (       ( $line =~ m/^[-${SPACE}]?[${HASH}]else\s+[\/]+\s+0/msx )
		|| ( $line =~ m/else\s+[\/]+\s+0\s+-->\s*$/msx )
		|| ( $line =~ m/\*\s+else\s+[\/]+\s+0\s+\*\*\/\s*$/msx ) )
	{
		return 1;
	} ## end if ( ( $line =~ m/^[-${SPACE}]?[${HASH}]else\s+[\/]+\s+0/msx...))

	return 0;
} ## end sub is_mask_else

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any mask end      ---
# --------------------------------------------------------------
sub is_mask_end {
	my ($line) = @_;

	defined($line) and length($line) or return 0;

	if (       ( $line =~ m,^[- ]?[${HASH}]endif\s*/(?:[*/]+)\s*(?:0),msx )
		|| ( $line =~ m,//\s+0\s+-->\s*$,msx )
		|| ( $line =~ m,\*\s+//\s+0\s+\*\*/\s*$,msx ) )
	{
		return 1;
	} ## end if ( ( $line =~ m,^[- ]?[${HASH}]endif\s*/(?:[*/]+)\s*(?:0),msx...))

	return 0;
} ## end sub is_mask_end

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any mask start    ---
# --------------------------------------------------------------
sub is_mask_start {
	my ($line) = @_;

	defined($line) and length($line) or return 0;

	if (
		( $line =~ m/^[-${SPACE}]?[${HASH}]if\s+0.+elogind/msx )
		|| ( ( $line =~ m/<!--\s+0.+elogind/msx )
			&& !( $line =~ m/-->\s*$/msx ) )
		|| ( ( $line =~ m,/\*\*\s+0.+elogind,msx )
			&& !( $line =~ m,\*\*/\s*$,msx ) )
	        )
	{
		return 1;
	} ## end if ( ( $line =~ m/^[-${SPACE}]?[${HASH}]if\s+0.+elogind/msx...))

	return 0;
} ## end sub is_mask_start

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
		@args = ($fmt);  ## Make the fixed string the first (and only) argument
		$fmt  = '%s';    ## And print it "as-is".
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

# -----------------------------------------------------------------------
# --- Prepare shell and meson files for our processing.               ---
# --- If this is a shell or meson file, we have to adapt it first:    ---
# --- To be able to use our patch building system, the files use the  ---
# --- same masking technology as the C files. But as these are not    ---
# --- handled by any preprocessor, it is necessary to comment out all ---
# --- masked blocks.                                                  ---
# --- If we do not do this, diff creates patches which move all       ---
# --- commented blocks behind the #endif and uncomment them.          ---
# -----------------------------------------------------------------------
sub prepare_shell {
	my $in   = $hFile{source};
	my $out  = $in . '.pwx';
	my @lIn  = ();
	my @lOut = ();

	# Leech the source file
	if ( open( my $fIn, "<", $in ) ) {
		@lIn = <$fIn>;
		close($fIn);
	} else {
		croak("$in can not be opened for reading! [$!]");
	}

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
		} elsif ( is_mask_else($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask else outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_else = 1;
		} elsif ( is_mask_end($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask end outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 0;
			$is_else  = 0;
		} elsif ( $is_block && !$is_else ) {
			$line =~ s/^[${HASH}]\s?//msgx;
			$line =~ s/^\s\s\*\s?//msgx;
		}

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open( my $fOut, ">", $out ) ) {
		for my $line (@lOut) {
			print $fOut "$line\n";
		}
		close($fOut);
	} else {
		croak("$out can not be opened for writing! [$!]");
	}

	# The temporary file is our new source
	$hFile{source} = $out;

	return 1;
} ## end sub prepare_shell

# -----------------------------------------------------------------------
# --- The masking of unneeded blocks in XML files is done using a     ---
# --- comment scheme. Unfortunately the standard forbids double dashes---
# --- in comments. To be able to process XML files nevertheless, they ---
# --- are updated by unprepare_xml() so that all double dashes in     ---
# --- comments are substituted by &#x2D;&#x2D;, which must be reversed---
# --- here or the further processing would go nuts.                   ---
# -----------------------------------------------------------------------
sub prepare_xml {
	my $in   = $hFile{source};
	my $out  = $in . ".pwx";
	my @lIn  = ();
	my @lOut = ();

	# Leech the source file
	if ( open( my $fIn, "<", $in ) ) {
		@lIn = <$fIn>;
		close($fIn);
	} else {
		croak("$in can not be opened for reading! [$!]");
	}

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
		} elsif ( is_mask_else($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask else outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_else = 1;
		} elsif ( is_mask_end($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask end outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 0;
			$is_else  = 0;
		} elsif ( $is_block && !$is_else ) {
			$line =~ s/&#x2D;/-/msg;
		}

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open( my $fOut, ">", $out ) ) {
		for my $line (@lOut) {
			print $fOut "$line\n";
		}
		close($fOut);
	} else {
		croak("$out can not be opened for writing! [$!]");
	}

	# The temporary file is our new source
	$hFile{source} = $out;

	return 1;
} ## end sub prepare_xml

# -----------------------------------------------------------------------
# --- Special function to not let diff add unwanted or remove our     ---
# --- lines in logind.conf.in (See Issue #2)                          ---
# -----------------------------------------------------------------------
sub protect_config() {

	# early exits:
	defined($hHunk)  or croak("check_masks: hHunk is undef");
	$hHunk->{useful} or croak("check_masks: Nothing done but hHunk is useless?");

	my $is_sleep_block = 0;
	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# Kill addition of lines we do not need
		# ---------------------------------------
		if ( $$line =~ m/^[${PLUS}][${HASH}]?(?:NAutoVTs|ReserveVT)/msx ) {
			splice( @{ $hHunk->{lines} }, $i--, 1 );
			--$hHunk->{count};
			next;
		}

		# enter elogind specific [Sleep] block
		# ------------------------------------------
		if ( $$line =~ m,^\-\[Sleep\], ) {
			substr( $$line, 0, 1 ) = " ";  ## Remove '-'

			# The previous line is probably the deletion of the blank line before the block
			( $i > 0 ) and ( $hHunk->{lines}[ $i - 1 ] =~ /^-/ ) and $hHunk->{lines}[ $i - 1 ] = " ";

			$is_sleep_block = 1;
			next;
		} ## end if ( $$line =~ m,^\-\[Sleep\],)

		# Remove deletions of lines in our [Sleep] block
		$is_sleep_block
		        and ( $$line =~ m,^[${DASH}], )
		        and substr( $$line, 0, 1 ) = " "  ## Remove '-'
		        and next;

		# No sleep block
		$is_sleep_block = 0;

	} ## end for ( my $i = 0 ; $i < ...)

	return 1;
} ## end sub protect_config

# -----------------------------------------------------------------------
# --- Remove unused prefix and postfix lines. Recalculates offsets.   ---
# -----------------------------------------------------------------------
sub prune_hunk() {

	# early exits:
	defined($hHunk)  or return 0;
	$hHunk->{useful} or return 0;

	log_debug("Pruning Hunk ...");

	# Go through the lines and see what we've got.
	my @mask_info = ( $hHunk->{masked_start} );
	my $prefix    = 0;
	my $postfix   = 0;
	my $changed   = 0;                          ## Set to 1 once the first change was found.

	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = $hHunk->{lines}[$i];     ## Shortcut
		if ( $line =~ m/^[-+]/ ) {
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
	} ## end for ( my $i = 0 ; $i < ...)

	# Now let's prune it:
	if ( $prefix > 3 ) {
		$prefix -= 3;
		log_debug( "  => Splicing first %d lines", $prefix );
		splice( @{ $hHunk->{lines} }, 0, $prefix );
		$hHunk->{src_start} += $prefix;
		$hHunk->{count}     -= $prefix;

		# If any mask state change gets pruned, we have to remember the last one:
		for ( my $i = $prefix ; $i >= 0 ; --$i ) {
			if ( $mask_info[$i] ) {
				$hHunk->{masked_start} = $mask_info[$i] > 0 ? 1 : 0;
				last;
			}
		} ## end for ( my $i = $prefix ;...)
	} ## end if ( $prefix > 3 )
	if ( $postfix > 3 ) {
		$postfix -= 3;
		log_debug( "  => Splicing last %d lines", $postfix );
		splice( @{ $hHunk->{lines} }, $hHunk->{count} - $postfix, $postfix );
		$hHunk->{count} -= $postfix;
	} ## end if ( $postfix > 3 )

	return 1;
} ## end sub prune_hunk

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
sub unprepare_shell {
	my $in   = $hFile{source};
	my $out  = substr( $in, 0, -4 );
	my @lIn  = ();
	my @lOut = ();

	# Do not handle XML files here
	$hFile{is_xml} and return 0;

	# Leech the temporary file
	if ( open( my $fIn, "<", $in ) ) {
		@lIn = <$fIn>;
		close($fIn);
	} else {
		croak("$in can not be opened for reading! [$!]");
	}

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
		} elsif ( is_mask_else($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask else outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_else = 1;
		} elsif ( is_mask_end($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask end outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 0;
			$is_else  = 0;
		} elsif (  $is_block
			&& !$is_else
			&& ( '# #' ne substr( $line, 0, 3 ) )
			&& ( '  * ' ne substr( $line, 0, 4 ) ) )
		{
			$hFile{source} =~ m/${DOT}sym${DOT}pwx$/msx and $line = '  * ' . $line
			        or $line = '# ' . $line;

			# Do not create empty comment lines with trailing spaces.
			$line =~ s/([${HASH}])\s+$/$1/msgx;
		} ## end elsif ( $is_block && !$is_else...)

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open( my $fOut, ">", $out ) ) {
		for my $line (@lOut) {
			print $fOut "$line\n";
		}
		close($fOut);
	} else {
		croak("$out can not be opened for writing! [$!]");
	}

	# Remove the temporary file
	unlink($in);

	# Now prepare the patch. It is like above, but with less checks.
	# We have to move out the lines first, and then write them back.
	$is_block = 0;
	$is_else  = 0;
	@lIn      = splice( @{ $hFile{output} } );

	for my $line (@lIn) {
		if ( $line =~ m/[${HASH}]\s+masked_(?:start|end)\s+([01])$/msx ) {
			$1        and $is_block = 1 or $is_block = 0;
			$is_block and $is_else  = 0;                  ## can't be.
			next;                                         ## do not transport this line
		}
		is_mask_end($line)   and $is_block = 0;
		is_mask_start($line) and $is_block = 1;
		$is_block or $is_else = 0;
		is_mask_else($line) and $is_else = 1;
		$is_block
		        and ( !$is_else )
		        and '@@' ne substr( $line, 0, 2 )
		        and ( !( $line =~ m/^[-${SPACE}]+[${HASH}](?:if|else|endif)/msx ) )
		        and substr( $line, 1, 0 ) = "# ";

		# Make sure not to demand to add empty comment lines with trailing spaces
		$line =~ s/^(\+[${HASH}])\s+$/$1/msgx;
		push @{ $hFile{output} }, $line;
	} ## end for my $line (@lIn)

	# Now source is the written back original:
	$hFile{source} = $out;

	return 1;
} ## end sub unprepare_shell

# -----------------------------------------------------------------------
# --- Before we can allow an XML file to live, all double dashes that ---
# --- happen to reside in one of our mask blocks must be masked.      ---
# --- The standard forbids double dashes inside comments, so we solve ---
# --- this by substituting '--' with '&#x2D;&#x2D;'.                  ---
# -----------------------------------------------------------------------
sub unprepare_xml {
	my $in   = $hFile{source};
	my $out  = substr( $in, 0, -4 );
	my @lIn  = ();
	my @lOut = ();

	# Do not handle shell files here
	$hFile{is_sh} and return 0;

	# Leech the temporary file
	if ( open( my $fIn, "<", $in ) ) {
		@lIn = <$fIn>;
		close($fIn);
	} else {
		croak("$in can not be opened for reading! [$!]");
	}

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
		} elsif ( is_mask_else($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask else outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_else = 1;
		} elsif ( is_mask_end($line) ) {
			if ( 0 == $is_block ) {
				log_error( '%s:%d : Mask end outside mask!', $in, $line_no );
				croak('Illegal file');
			}
			$is_block = 0;
			$is_else  = 0;
		} elsif ( $is_block && !$is_else ) {
			$line =~ s/--/&#x2D;&#x2D;/msg;
		}

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open( my $fOut, ">", $out ) ) {
		for my $line (@lOut) {
			print $fOut "$line\n";
		}
		close($fOut);
	} else {
		croak("$out can not be opened for writing! [$!]");
	}

	# Remove the temporary file
	unlink($in);

	# Now prepare the patch. It is like above, but with less checks.
	# We have to move out the lines first, and then write them back.
	@lIn      = ();
	$is_block = 0;
	$is_else  = 0;
	@lIn      = splice( @{ $hFile{output} } );
	for my $line (@lIn) {
		if ( $line =~ m/[${HASH}]\s+masked_(?:start|end)\s+([01])$/msx ) {
			$1        and $is_block = 1 or $is_block = 0;
			$is_block and $is_else  = 0;                  ## can't be.
			next;                                         ## do not transport this line
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

# -----------------------------------------------------------------------
# --- Analyze the hunk and map all include changes                    ---
# --- The gathered knowledge is used in check_includes(), see there   ---
# --- for the rules applied.                                          ---
# -----------------------------------------------------------------------
sub read_includes {

	# early exits:
	defined($hHunk)  or return 1;
	$hHunk->{useful} or return 1;

	# We must know when "needed by elogind blocks" start
	my $in_elogind_block = 0;
	for ( my $i = 0 ; $i < $hHunk->{count} ; ++$i ) {
		my $line = \$hHunk->{lines}[$i];  ## Shortcut

		# Note down removals of includes we commented out
		if ( $$line =~ m/^[${DASH}]\s*\/[\/*]+\s*[${HASH}]include\s+([<"'])([^>"']+)[>"']\s*(?:\*\/)?/msx ) {
			$hIncs{$2}{remove} = {
				hunkid => $hHunk->{idx},
				lineid => $i,
				sysinc => $1 eq "<"
			};
			next;
		} ## end if ( $$line =~ m/^[${DASH}]\s*\/[\/*]+\s*[${HASH}]include\s+([<"'])([^>"']+)[>"']\s*(?:\*\/)?/msx)

		# Note down inserts of possibly new includes we might want commented out
		if ( $$line =~ m/^[${PLUS}]\s*[${HASH}]include\s+([<"'])([^>"']+)[>"']/msx ) {
			$hIncs{$2}{insert} = {
				elogind  => $in_elogind_block,
				hunkid   => $hHunk->{idx},
				lineid   => $i,
				spliceme => 0,
				sysinc   => $1 eq "<"
			};
			next;
		} ## end if ( $$line =~ m/^[${PLUS}]\s*[${HASH}]include\s+([<"'])([^>"']+)[>"']/msx)

		# Note down removals of includes we explicitly added for elogind
		if ( $in_elogind_block && ( $$line =~ m/^[${DASH}]\s*[${HASH}]include\s+([<"'])([^>"']+)[>"']/msx ) ) {
			$hIncs{$2}{elogind} = { hunkid => $hHunk->{idx}, lineid => $i };
			next;
		}

		# elogind include blocks are started by a comment featuring "needed by elogind"
		if ( $$line =~ m,^[ -]\s*/+.*needed\s+(?:by|for)\s+elogind.*,msxi ) {
			$in_elogind_block = 1;
			next;
		}

		# elogind include blocks end, when the first not removed *EMPTY* line is found
		$in_elogind_block and ( $$line =~ m,^[ ]\s*$, ) and $in_elogind_block = 0;
	} ## end for ( my $i = 0 ; $i < ...)

	return 1;
} ## end sub read_includes

sub set_log_file {
	my ($name) = @_;
	$logfile = sprintf '%s-%s.log', $name, get_date_now();
	return 1;
}

sub show_progress {
	my ( $log_as_status, $fmt, @args ) = @_;
	my $progress_str = sprintf $fmt, @args;

	# Clear a previous progress line
	( $have_progress_msg > 0 ) and print "\r" . ( $SPACE x length $progress_str ) . "\r";

	if ( 0 < $log_as_status ) {

		# Write into log file
		$have_progress_msg = 0;  ## ( We already deleted the line above, leaving it at 1 would add a useless empty line. )
		log_status( '%s', $progress_str );
	} else {

		# Output on console
		$have_progress_msg = 1;
		local $| = 1;
		print "\r${progress_str}";
	} ## end else [ if ( 0 < $log_as_status)]

	return 1;
} ## end sub show_progress

# ---------------------------------------------------------
# A signal handler that sets global vars according to the
# signal given.
# Unknown signals are ignored.
# ---------------------------------------------------------
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

# -----------------------------------------------------------------------
# --- Splice all includes that were marked for splicing.              ---
# --- This is not as easy as it seems. It can be, that if we just go  ---
# --- through the %hIncs keys, that we splice one include that is     ---
# --- before another. That leads to the wrong line to be spliced, or  ---
# --- worse, the splicing being attempted out of bounds.              ---
# -----------------------------------------------------------------------
sub splice_includes {

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
		for my $lId ( sort { $b <=> $a } keys %{ $incMap{$hId} } ) {
			splice( @{ $hFile{hunks}[$hId]{lines} }, $lId, 1 );
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

# Callback function for File::Find
sub wanted {
	my $f         = $File::Find::name;
	my $is_wanted = 0;

	$f =~ m,^\./, or $f = "./$f";

	-f $_
	        and ( ( 0 == $have_wanted ) or defined( $hWanted{$f} ) )
	        and ( !( $_                =~ m/\.pwx$/ ) )
	        and ( !( $File::Find::name =~ m,man/rules/, ) )  ## Protect generated man rules (Issue #3)
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

sub write_to_console {
	my ($msg) = @_;

	if ( $have_progress_msg > 0 ) {
		print "\n";
		$have_progress_msg = 0;
	}

	local $| = 1;
	return print "${msg}\n";
} ## end sub write_to_console

sub write_to_log {
	my ($msg) = @_;

	if ( open my $fLog, '>>', $logfile ) {
		print {$fLog} "${msg}\n";
		close $fLog or confess("Closing logfile '$logfile' FAILED!");
	}

	return 1;
} ## end sub write_to_log

__END__


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

The path to the upstream tree tro compare with is the only mandatory argument.


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
