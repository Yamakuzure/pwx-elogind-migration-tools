#!/usr/bin/perl -w

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
# 0.8.5    2018-03-13  sed, PrydeWorX  Added possibility to (manualy) check root files and enhanced the
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
# 1.4.0    2023-05-12  sed, EdenWorX   Fix accidential renaming of systemd-only apps and revert reversals into mask blocks.
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
use strict;
use warnings;
use Cwd qw( getcwd abs_path );
use File::Basename;
use File::Find;
use Git::Wrapper;
use Readonly;
use Try::Tiny;

# ================================================================
# ===        ==> ------ Help Text and Version ----- <==        ===
# ================================================================
Readonly my $VERSION => "1.4.2"; ## Please keep this current!
Readonly my $VERSMIN => "-" x length( $VERSION );
Readonly my $PROGDIR => dirname( $0 );
Readonly my $PROGNAME => basename( $0 );
Readonly my $WORKDIR => getcwd();
Readonly my $USAGE_SHORT => "$PROGNAME <--help|[OPTIONS] <path to upstream tree>>";
Readonly my $USAGE_LONG => qq#
elogind git tree checker V$VERSION
--------------------------$VERSMIN

    Check the current tree, from where this program is called, against an
    upstream tree for changes, and generate a patchset out of the differences,
    that does not interfere with elogind development markings.

Usage :
-------
  $USAGE_SHORT

  The path to the upstream tree should have the same layout as the place from
  where this program is called. It is best to call this program from the
  elogind root path and use a systemd upstream root path for comparison.

Options :
---------
    -c|--commit <refid> | Check out <refid> in the upstream tree.
       --create         | Needs --file. If the file does not exist, create it.
    -f|--file   <path>  | Do not search recursively, check only <path>.
                        | For the check of multiple files, you can either
                        | specify -f multiple times, or concatenate paths with
                        | a comma, or mix both methods.
    -h|--help           | Print this help text and exit.
       --stay           | Needs --commit. Do not reset to the current commit,
                        | stay with the wanted commit.
#;

# ================================================================
# ===       ==> -------- File name patterns -------- <==       ===
# ================================================================
Readonly my %FILE_NAME_PATTERNS => (
	"shell" => [
		'LINGUAS',
		'Makefile',
		'meson',
		'\.gitignore$',
		'\.gperf$',
		'\.in$',
		'\.m4$',
		'\.pl$',
		'\.po$',
		'\.pot$',
		'\.py$',
		'\.sh$',
		'\.sym$',
		'bash/busctl',
		'bash/loginctl',
		'pam.d/other',
		'pam.d/system-auth',
		'zsh/_busctl',
		'zsh/_loginctl'
	],
	"xml"   => [
		'\.xml$',
		'\.ent\.in$',
		'\.policy\.in$/'
	]
);

# And some protected website URLs
Readonly my %SYSTEMD_URLS => (
	'fedoraproject.org/projects/systemd' => 1,
	'freedesktop.org/software/systemd'   => 1
);

# ================================================================
# ===        ==> -------- Global variables -------- <==        ===
# ================================================================
my $do_create       = 0;  ## If set to 1, a non-existing file is created.
my $do_stay         = 0;  ## If set to 1, the previous commit isn't restored on exit.
my $file_fmt        = ""; ## Format string built from the longest file name in generate_file_list().
my $have_wanted     = 0;  ## Helper for finding relevant files (see wanted())
my %hToCreate       = (); ## The keys are files that do not exist and shall be created.
my %hWanted         = (); ## Helper hash for finding relevant files (see wanted())
my $in_else_block   = 0;  ## Set to 1 if we switched from mask/unmask to 'else'.
my $in_glibc_block  = 0;  ## Set to 1 if we enter a __GLIBC__ block
my $in_mask_block   = 0;  ## Set to 1 if we entered an elogind mask block
my $in_insert_block = 0;  ## Set to 1 if we entered an elogind addition block
my $main_result     = 1;  ## Used for parse_args() only, as simple $result is local everywhere.
my @only_here       = (); ## List of files that do not exist in $upstream_path.
my $previous_commit = ""; ## Store current upstream state, so we can revert afterwards.
my $show_help       = 0;
my @source_files    = (); ## Final file list to process, generated in in generate_file_list().
my $upstream_path   = "";
my $wanted_commit   = "";
my @wanted_files    = (); ## User given file list (if any) to limit generate_file_list()

# ================================================================
# ===        ==> ------- MAIN DATA STRUCTURES ------ <==       ===
# ================================================================
my %hFile = (); ## Main data structure to manage a complete compare of two files. (See: build_hFile() )
# Note: %hFile is used globaly for each file that is processed.
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
my $hHunk = {}; ## Secondary data structure to describe one diff hunk.            (See: build_hHunk() )
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
my %hIncs = (); ## Hash for remembered includes over different hunks.
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
my %hProtected = (); ## check_name_reverts() writes notes down lines here, which check_comments() shall not touch
my @lFails     = (); ## List of failed hunks. These are worth noting down in an extra structure, as these
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

sub build_hFile;        ## Inititializes and fills %hFile.
sub build_hHunk;        ## Adds a new $hFile{hunks}[] instance.
sub build_output;       ## Writes $hFile{output} from all useful $hFile{hunks}.
sub check_blanks;       ## Check that useful blank line additions aren't misplaced.
sub check_comments;     ## Check comments we added for elogind specific information.
sub check_debug;        ## Check for debug constructs
sub check_empty_masks;  ## Check for empty mask blocks, remove them and leave a note.
sub check_func_removes; ## Check for attempts to remove elogind_*() special function calls.
sub check_includes;     ## performe necessary actions with the help of %hIncs (built by read_includes())
sub check_masks;        ## Check for elogind preprocessor masks
sub check_musl;         ## Check for musl_libc compatibility blocks
sub check_name_reverts; ## Check for attempts to revert 'elogind' to 'systemd'
sub check_sym_lines;    ## Check for attempts to uncomment unsupported API functions in .sym files.
sub check_useless;      ## Check for useless updates that do nothing.
sub checkout_upstream;  ## Checkout the given refid on $upstream_path
sub clean_hFile;        ## Completely clean up the current %hFile data structure.
sub diff_hFile;         ## Generates the diff and builds $hFile{hunks} if needed.
sub generate_file_list; ## Find all relevant files and store them in @wanted_files
sub get_hunk_head;      ## Generate the "@@ -xx,n +yy,m @@" hunk header line out of $hHunk.
sub hunk_failed;        ## Generates a new @lFails entry and terminates the progress line.
sub hunk_is_useful;     ## Prunes the hunk and checks whether it stil does anything
sub is_insert_end;      ## Return 1 if the argument consists of any insertion end
sub is_insert_start;    ## Return 1 if the argument consists of any insertion start
sub is_mask_else;       ## Return 1 if the argument consists of any mask else
sub is_mask_end;        ## Return 1 if the argument consists of any mask end
sub is_mask_start;      ## Return 1 if the argument consists of any mask start
sub parse_args;         ## Parse ARGV for the options we support
sub prepare_shell;      ## Prepare shell (and meson) files for our processing
sub prepare_xml;        ## Prepare XML files for our processing (Unmask double dashes in comments)
sub protect_config;     ## Special function to not let diff add unwanted or remove our lines in logind.conf.in
sub prune_hunk;         ## remove unneeded prefix and postfix lines.
sub read_includes;      ## map include changes
sub splice_includes;    ## Splice all includes that were marked for splicing
sub unprepare_shell;    ## Unprepare shell (and meson) files after our processing
sub unprepare_xml;      ## Unprepare XML files after our processing (Mask double dashes in comments)
sub wanted;             ## Callback function for File::Find

# ================================================================
# ===        ==> --------    Prechecks     -------- <==        ==
# ================================================================

$main_result = parse_args( @ARGV );
(
	( !$main_result ) ## Note: Error or --help given, then exit.
	or ( $show_help and print "$USAGE_LONG" ) ) and exit( !$main_result );
length( $wanted_commit )
and (
	checkout_upstream( $wanted_commit ) ## Note: Does nothing if $wanted_commit is already checked out.
	or exit 1
);
generate_file_list or exit 1; ## Note: @wanted_files is heeded.

# ================================================================
# ===        ==> -------- = MAIN PROGRAM = -------- <==        ===
# ================================================================

for my $file_part ( @source_files ) {
	printf( "$file_fmt: ", $file_part );

	build_hFile( $file_part ) or next;
	diff_hFile or next;

	# Reset global state helpers
	$in_else_block   = 0;
	$in_glibc_block  = 0;
	$in_mask_block   = 0;
	$in_insert_block = 0;

	# Empty the include manipulation hash
	%hIncs = ();

	# ---------------------------------------------------------------------
	# --- Go through all hunks and check them against our various rules ---
	# ---------------------------------------------------------------------
	for ( my $pos = 0; $pos < $hFile{count}; ++$pos ) {
		$hHunk    = $hFile{hunks}[$pos]; ## Global shortcut

		# === Special 1) protect src/login/logind.conf.in =================
		if ( $hFile{source} =~ m,src/login/logind.conf.in, ) {
			protect_config and hunk_is_useful and prune_hunk or next;
		}

		# === 1) Check for elogind masks 1 (normal source code) ===========
		check_masks and hunk_is_useful and prune_hunk or next;

		# === 2) Check for elogind masks 2 (symbol files) =================
		check_sym_lines and hunk_is_useful and prune_hunk or next;

		# === 3) Check for musl_libc compatibility blocks =================
		check_musl and hunk_is_useful and prune_hunk or next;

		# === 4) Check for debug constructs ===============================
		check_debug and hunk_is_useful and prune_hunk or next;

		# === 5) Check for useful blank line additions ====================
		check_blanks and hunk_is_useful and prune_hunk or next;

		# === 6) Check for 'elogind' => 'systemd' reverts =================
		%hProtected = ();
		check_name_reverts and hunk_is_useful and prune_hunk or next;

		# === 7) Check for elogind_*() function removals ==================
		check_func_removes and hunk_is_useful and prune_hunk or next;

		# === 8) Check for elogind extra comments and information =========
		check_comments and hunk_is_useful and prune_hunk or next;

		# === 9) Check for any useless changes that do nothing ============
		check_useless and hunk_is_useful and prune_hunk or next;

		# === 10) Check for empty masks that guard nothing any more =======
		check_empty_masks and hunk_is_useful and prune_hunk or next;

		#  ===> IMPORTANT: From here on no more pruning, lines must *NOT* change any more! <===

		# === 11) Analyze includes and note their appearance in $hIncs =====
		read_includes; ## Never fails, doesn't change anything.

	} ## End of first hunk loop

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
	for ( my $pos = 0; $pos < $hFile{count}; ++$pos ) {
		$hHunk    = $hFile{hunks}[$pos]; ## Global shortcut

		# (pre -> early out)
		hunk_is_useful or next;

		# === 1) Apply what we learned about changed includes =============
		check_includes and hunk_is_useful or next;

	} ## End of second hunk loop

	# ---------------------------------------------------------------------
	# --- Splice all include insertions that are marked for splicing    ---
	# ---------------------------------------------------------------------
	splice_includes;

	# ---------------------------------------------------------------------
	# --- Go through all hunks for a last prune and check               ---
	# ---------------------------------------------------------------------
	my $have_hunk = 0;
	for ( my $pos = 0; $pos < $hFile{count}; ++$pos ) {
		$hHunk    = $hFile{hunks}[$pos]; ## Global shortcut

		# (pre -> early out)
		hunk_is_useful or next;

		prune_hunk and ++$have_hunk;
	} ## end for ( my $pos = 0 ; $pos...)

	# If we have at least 1 useful hunk, create the output and tell the user what we've got.
	$have_hunk
	and build_output # (Always returns 1)
	and printf( "%d Hunk%s\n", $have_hunk, $have_hunk > 1 ? "s" : "" )
	or print( "clean\n" );

	# Shell and xml files must be unprepared. See unprepare_[shell,xml]()
	$hFile{pwxfile} and ( unprepare_shell or unprepare_xml );

	# Now skip the writing if there are no hunks
	$have_hunk or next;

	# That's it, write the file and be done!
	if ( open( my $fOut, ">", $hFile{patch} ) ) {
		for my $line ( @{ $hFile{output} } ) {

			# Do not assume empty comment lines with trailing spaces in shell files
			$hFile{pwxfile} and $line =~ s/([+ -]#)\s+$/$1/;
			print $fOut "$line\n";
		} ## end for my $line ( @{ $hFile...})
		close( $fOut );
	} else {
		printf( "ERROR: %s could not be opened for writing!\n%s\n", $hFile{patch}, $! );
		die( "Please fix this first!" );
	}
} ## End of main loop

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
		my $fmt   = sprintf( "%%d %d: %%s\n", length( "$count" ));

		printf( "\n%d file%s only found in $WORKDIR:\n", $count, $count > 1 ? "s" : "" );

		for ( my $i = 0; $i < $count; ++$i ) {
			printf( $fmt, $i + 1, $only_here[$i] );
		}
	} ## end if ( scalar @only_here)

	# -------------------------------------------------------------------------
	# --- Print out the list of failed hunks -> bug in hunk or program?     ---
	# -------------------------------------------------------------------------
	if ( scalar @lFails ) {
		my $count = scalar @lFails;

		printf( "\n%d file%s %s at least one fishy hunk:\n", $count, $count > 1 ? "s" : "",
		        $count > 1 ? "have" : "has" );

		for ( my $i = 0; $i < $count; ++$i ) {
			print "=== $lFails[$i]{part} ===\n";
			print " => $lFails[$i]{msg} <=\n";
			print "---------------------------\n";
			print " {count}        : \"" . $lFails[$i]{info}{count} . "\"\n";
			print " {idx}          : \"" . $lFails[$i]{info}{idx} . "\"\n";
			print " {masked_end}   : \"" . $lFails[$i]{info}{masked_end} . "\"\n";
			print " {masked_start} : \"" . $lFails[$i]{info}{masked_start} . "\"\n";
			print " {offset}       : \"" . $lFails[$i]{info}{offset} . "\"\n";
			print " {src_start}    : \"" . $lFails[$i]{info}{src_start} . "\"\n";
			print " {tgt_start}    : \"" . $lFails[$i]{info}{tgt_start} . "\"\n";
			print " {useful}       : \"" . $lFails[$i]{info}{useful} . "\"\n";
			print "---------------------------\n";
			print "$_\n" foreach ( @{ $lFails[$i]{hunk} } );
		} ## end for ( my $i = 0 ; $i < ...)
	}     ## end if ( scalar @lFails )

	$do_stay or length( $previous_commit ) and checkout_upstream( $previous_commit );
} ## end END

# ================================================================
# ===        ==> ---- Function Implementations ---- <==        ===
# ================================================================

# -----------------------------------------------------------------------
# --- Inititializes and fills %hFile. Old values are discarded.       ---
# --- Adds files, that do not exist upstream, to @only_here.          ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub build_hFile {
	my ( $part ) = @_;

	defined( $part ) and length( $part ) or print( "ERROR\n" ) and die( "build_hfile: part is empty ???" );

	# Is this a new file?
	my $isNew = defined( $hToCreate{$part} ) ? 1 : 0;

	# We only prefixed './' to unify things. Now it is no longer needed:
	$part =~ s,^\./,,;

	# Pre: erase current $hFile, as that is what is expected.
	clean_hFile();

	# Check the target file
	my $tgt = "$upstream_path/$part";
	$tgt =~ s/elogind/systemd/g;
	$tgt =~ s/\.pwx$//;
	-f $tgt
	or push( @only_here, $part )
	   and print "only here\n"
	   and return 0;

	# Build the patch name
	my $patch = $part;
	$patch =~ s/\//_/g;

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
	my $pos              = $hFile{count}++;
	my $mark             = '@@';

	# The first line must be the hunk positional and size data.
	# Example: @@ -136,6 +136,8 @@
	# That is @@ -<source line>,<source length> +<target line>,<target length> @@
	if ( $head =~ m/^${mark} -(\d+),\d+ \+(\d+),\d+ ${mark}/ ) {
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
		for my $line ( @lHunk ) {
			defined( $line ) or next;
			chomp $line;
			push @{ $hFile{hunks}[$pos]{lines} }, $line;
			$hFile{hunks}[$pos]{count}++;
		} ## end for my $line (@lHunk)
		return 1;
	} ## end if ( $head =~ m/^@@ -(\d+),\d+ \+(\d+),\d+ @@/)

	print "Illegal hunk no $hFile{count}\n(Head: \"$head\")\nIgnoring...";
	$hFile{count}--;

	return 0;
} ## end sub build_hHunk

# -----------------------------------------------------------------------
# --- Writes $hFile{output} from all useful $hFile{hunks}.            ---
# --- Important: No more checks, just do it!                          ---
# -----------------------------------------------------------------------
sub build_output {

	my $offset = 0; ## Count building up target offsets

	for ( my $pos = 0; $pos < $hFile{count}; ++$pos ) {
		$hHunk    = $hFile{hunks}[$pos]; ## Global shortcut

		# The useless are to be skipped, but we need the hunks masked_end
		if ( $hHunk->{useful} ) {

			# --- Note down the relevant starting mask status ---
			# ---------------------------------------------------
			defined( $hHunk->{masked_start} ) and ( 1 == length( "$hHunk->{masked_start}" ) )
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
			push( @{ $hFile{output} }, get_hunk_head( \$offset ));

			# --- Add the hunk lines ----------------------------
			# ---------------------------------------------------
			for my $line ( @{ $hHunk->{lines} } ) {
				push( @{ $hFile{output} }, $line );
			}
		} ## end if ( $hHunk->{useful} )

		# --- Note down the relevant ending mask status -----
		# ---------------------------------------------------
		defined( $hHunk->{masked_end} ) and ( 1 == length( "$hHunk->{masked_end}" ) )
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

	} ## End of walking the hunks

	return 1;
} ## end sub build_output

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

	# Early exits:
	defined( $hHunk ) or return 0;
	$hHunk->{useful} or return 0;

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Check for misplaced addition
		if ( ( $$line =~ m/^\+\s*$/ )
		     && ( $i > 0 )
		     && ( ( is_mask_start( $hHunk->{lines}[ $i - 1 ] ) || is_insert_start( $hHunk->{lines}[ $i - 1 ] ) ) ) ) {
			# Simply swap the lines
			my $tmp                   = $$line;
			$$line                    = $hHunk->{lines}[ $i - 1 ];
			$hHunk->{lines}[ $i - 1 ] = $tmp;
			next;
		} ## end if ( ( $$line =~ m/^\+\s*$/...))

		# Check for unpleasant removals
		if ( ( $$line =~ m/^\-\s*$/ )
		     && ( $i > 0 )
		     && ( ( is_mask_end( $hHunk->{lines}[ $i - 1 ] ) || is_insert_end( $hHunk->{lines}[ $i - 1 ] ) ) )
		     && ( $i < ( $hHunk->{count} - 1 ) )
		     && ( !( $hHunk->{lines}[ $i + 1 ] =~ m/^[-+ ]\s*$/ ) ) ) {
			# Revert the removal
			substr( $$line, 0, 1 ) = " ";
			next;
		} ## end if ( ( $$line =~ m/^\+\s*$/...))

	} ## end for ( my $i = 0 ; $i < ...)

	return 1;
} ## end sub check_blanks

# -----------------------------------------------------------------------
# --- Check comments we added for elogind specific information.       ---
# --- These are all comments, and can be both single and multi line.  ---
# -----------------------------------------------------------------------
sub check_comments {

	# Early exits:
	defined( $hHunk ) or return 0;
	$hHunk->{useful} or return 0;

	my $in_comment_block = 0;

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Ignore protected lines
		defined( $hProtected{$$line} ) and next;

		# Check for comment block start
		# -----------------------------
		if ( $$line =~ m,^-\s*(/\*+|//+)\s+.*elogind, ) {

			# Sanity check:
			$in_comment_block
			and return hunk_failed( "check_comments: Comment block start found in comment block!" );

			# Only start the comment block if this is really a multiline comment
			( ( $$line =~ m,^-\s*/\*+, ) && !( $$line =~ m,\*/[^/]*$, ) )
			and $in_comment_block = 1;

			# Revert the substract *if* this is not in a mask block
			$in_mask_block and ( 1 > $in_else_block ) or substr( $$line, 0, 1 ) = " ";

			next;
		} ## end if ( $$line =~ m,^-\s*(/[*]+|/[/]+).*elogind,)

		# Check for comment block end
		# -----------------------------
		if ( $in_comment_block && ( $$line =~ m,^-.*\*/\s*$, ) ) {
			substr( $$line, 0, 1 ) = " ";
			$in_comment_block      = 0;
			next;
		}

		# Check for comment block line
		# -----------------------------
		if ( $in_comment_block && ( $$line =~ m,^-, ) ) {

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

	# Early exits:
	defined( $hHunk ) or return 0;
	$hHunk->{useful} or return 0;

	# Count non-elogind block #ifs. This is needed, so normal
	# #if/#else/#/endif constructs can be put inside both the
	# debug and the release block.
	my $regular_ifs   = 0;
	my $is_debug_func = 0; ## Special for log_debug_elogind()

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Entering a debug construct block
		# ---------------------------------------
		if ( $$line =~ m/^-#if.+ENABLE_DEBUG_ELOGIND/ ) {
			## Note: Here it is perfectly fine to be in an elogind mask or insert block.
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_insert_block++;           ## Increase instead of setting this to 1.
			next;
		} ## end if ( $$line =~ m/^-#if.+ENABLE_DEBUG_ELOGIND/)

		# Count regular #if
		$$line =~ m/^-#if/ and ++$regular_ifs;

		# Switching to the release variant.
		# ---------------------------------------
		if ( ( $$line =~ m/^-#else/ ) && $in_insert_block && !$regular_ifs ) {
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_else_block++;             ## Increase instead of setting this to 1.
			next;
		}

		# Ending a debug construct block
		# ---------------------------------------
		if ( $$line =~ m,^-#endif\s*///?.*ENABLE_DEBUG_, ) {
			( !$in_insert_block )
			and return hunk_failed( "check_debug: #endif // ENABLE_DEBUG_* found outside any debug construct" );
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_insert_block--;           ## Decrease instead of setting to 0. This allows such
			$in_else_block--;             ## blocks to reside in regular elogind mask/insert blocks.
			next;
		} ## end if ( $$line =~ m,^-#endif\s*///?.*ENABLE_DEBUG_,)

		# End regular #if
		$$line =~ m/^-#endif/ and --$regular_ifs;

		# Check for log_debug_elogind()
		# ---------------------------------------
		if ( $$line =~ m/^-.*log_debug_elogind\s*\(/ ) {
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$$line =~ m/\)\s*;/ or ++$is_debug_func;
			next;
		}

		# Remove '-' prefixes in all lines within the debug construct block
		# -------------------------------------------------------------------
		if ( ( $$line =~ m,^-, ) && ( $in_insert_block || $is_debug_func ) ) {
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			# Note: Everything in *any* insert block must not be removed anyway.
		}

		# Check for the end of a multiline log_debug_elogind() call
		# ---------------------------------------------------------
		$is_debug_func and $$line =~ m/\)\s*;/ and --$is_debug_func;

	} ## End of looping lines

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

	# Early exits:
	defined( $hHunk ) or return 1;
	$hHunk->{useful} or return 1;

	# Not used in pwx files (meson, xml, sym)
	$hFile{pwxfile} and return 1;

	# Needed for multi-line calls
	my $is_func_call = 0;

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Ignore protected lines
		defined( $hProtected{$$line} ) and next;

		# Check for elogind_*() call
		# -------------------------------------------------------------------
		if ( $$line =~ m/^-.*elogind_\S+\s*\(/ ) {
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$$line =~ m/\)\s*;/ or ++$is_func_call;
			next;
		}

		# Remove '-' prefixes in all lines that belong to an elogind_*() call
		# -------------------------------------------------------------------
		if ( ( $$line =~ m,^-, ) && $is_func_call ) {
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
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

	# Early exits:
	defined( $hHunk ) or return 1;
	$hHunk->{useful} or return 1;

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

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Entering an elogind mask
		# ---------------------------------------
		if ( is_mask_start( $$line ) ) {
			# No checks needed, check_masks() already did that, and later pruning might make 
			# checks here fail, if large else block removals got reverted and the hunk(s) pruned.
			$local_iib = 0;
			$local_imb = 1;

			$mask_block_start = $i;

			# Note down mask message in case we leave a message
			$$line =~ m,///\s*(.+)\s*$, and $mask_message = $1;

			next;
		} ## end if ( is_mask_start($$line...))

		# Entering an elogind insert
		# ---------------------------------------
		if ( is_insert_start( $$line ) ) {
			$local_iib = 1;
			$local_ieb = 0;

			# Note down mask message in case we leave a message
			$$line =~ m,///\s*(.+)\s*$, and $mask_message = $1;

			next;
		} ## end if ( is_insert_start($$line...))

		# Count regular #if
		$$line =~ m/^-#if/ and ++$regular_ifs;

		# Switching from Mask to else.
		# Note: Inserts have no #else, they make no sense.
		# ---------------------------------------
		if ( is_mask_else( $$line ) ) {
			$local_ieb = 1;

			# If the else starts right after a mask start, we have to do something about it, if there is enough space left in the patch
			# (Which should be the case as the else block would have lengthened it. But better check it to be safe!)
			if ( $i && ( $i == ( $mask_block_start + 1 ) ) && ( $i < ( $hHunk->{count} - 2 ) ) ) {

				# Re-enable the removal of the "#if 0" and of the "#else" line
				substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = "-";
				substr( $hHunk->{lines}[$i], 0, 1 )       = "-";

				# Add a note that we converted this and add an insert mask
				splice( @{ $hHunk->{lines} }, $i + 1, 0, (
					"+/// elogind empty mask else converted",
					"+#if 1 /// $mask_message" ) );

				$hHunk->{count}        += 2;
				$need_endif_conversion = 1;
				$i                     += 2; ## Already known...
			}                                ## end if ( $i == ( $mask_block_start...))

			$mask_block_start = -1;

			next;
		} ## end if ( $local_imb && !$regular_ifs...)

		# Ending a Mask block
		# ---------------------------------------
		if ( is_mask_end( $$line ) ) {

			# If the endif is right after the mask start, we have to do something about it, but only if we have enough space left in the patch
			if ( $i < ( $hHunk->{count} - 2 ) ) {
				if ( $i && ( $i == ( $mask_block_start + 1 ) ) ) {

					# Re-enable the removal of the "#if 0" and of the "#endif" line
					substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = "-";
					substr( $hHunk->{lines}[$i], 0, 1 )       = "-";

					# Add a note that we converted this
					splice( @{ $hHunk->{lines} }, $i + 1, 0, ( '+' . ( $hFile{is_sh} ? '# ' : '' ) . "/// elogind empty mask removed ($mask_message)" ) );

					$hHunk->{count} += 1;
				} ## end if ( $i == ( $mask_block_start...))

				# If we need an endif conversion, do it now:
				elsif ( $need_endif_conversion > 0 ) {

					# First re-enable the removal:
					substr( $hHunk->{lines}[$i], 0, 1 ) = "-";

					# Add the correct endif
					splice( @{ $hHunk->{lines} }, $i + 1, 0, ( "+#endif // 1" ) );

					$hHunk->{count} += 1;
					$i              += 1; ## Already known...
				}                         ## end if ($need_endif_conversion)
			}

			$local_imb             = 0;
			$local_ieb             = 0;
			$mask_block_start      = -1;
			$mask_message          = "";
			$need_endif_conversion = 0;

			next;
		} ## end if ( is_mask_end($$line...))

		# Ending an insert block
		# ---------------------------------------
		if ( is_insert_end( $$line ) ) {
			$local_iib             = 0;
			$local_ieb             = 0;
			$mask_block_start      = -1;
			$mask_message          = "";
			$need_endif_conversion = 0;

			next;
		} ## end if ( is_insert_end($$line...))

		# End regular #if
		$$line =~ m/^-#endif/ and --$regular_ifs;

	} ## End of looping lines

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

	# Early exits:
	defined( $hHunk ) or return 1;
	$hHunk->{useful} or return 1;

	# We must know when "needed by elogind blocks" start
	my $in_elogind_block = 0;

	# The simple undo check will fail, if we do at least one at once.
	# Delay the undoing of the removals until after the hunk was checked.
	my %undos = ();

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# === Ruleset 1 : Handling of removals of includes we commented out ===
		# =====================================================================
		if ( $$line =~ m,^-\s*/[/*]+\s*#include\s+[<"']([^>"']+)[>"']\s*(?:\*/)?, ) {
			$hIncs{$1}{applied} and next; ## No double handling

			my $inc = $1;

			# Pre: Sanity check:
			defined( $hIncs{$inc}{remove}{hunkid} ) and $hIncs{$inc}{remove}{hunkid} > -1
			or return hunk_failed( "check_includes: Unrecorded removal found!" );

			# a) Check for removals of obsolete includes.
			$hIncs{$inc}{elogind}{hunkid} > -1   ## If no insert was found, then the include was
			or $hIncs{$inc}{insert}{hunkid} > -1 ## removed by systemd devs for good.
			or ( ++$hIncs{$inc}{applied} and next );

			# b) Check for a simple undo of our commenting out
			if ( ( $hIncs{$inc}{insert}{hunkid} == $hIncs{$inc}{remove}{hunkid} )
			     && ( $hIncs{$inc}{insert}{sysinc} == $hIncs{$inc}{remove}{sysinc} ) ) {
				my $ins_diff  = $hIncs{$inc}{insert}{lineid} - $hIncs{$inc}{remove}{lineid};
				my $all_same  = 1;
				my $direction = $ins_diff > 0 ? 1 : -1;

				# Let's see whether there are undos between this and its addition
				# in the same order, meaning there has been no resorting.
				for ( my $j   = $direction; ( $all_same > 0 ) && ( abs( $j ) < abs( $ins_diff ) ); $j += $direction ) {
					$all_same = 0;

					if ( ( $hHunk->{lines}[ $i + $j ] =~ m,^-\s*/[/*]+\s*#include\s+[<"']([^>"']+)[>"']\s*(?:\*/)?, )
					     || ( $hHunk->{lines}[ $i + $j ] =~ m,^\+\s*#include\s+[<"']([^>"']+)[>"'], ) ) {

						$hIncs{$1}{insert}{hunkid} == $hIncs{$1}{remove}{hunkid}
						and $ins_diff == ( $hIncs{$1}{insert}{lineid} - $hIncs{$1}{remove}{lineid} )
						and $hIncs{$inc}{insert}{sysinc} == $hIncs{$inc}{remove}{sysinc}
						and $all_same = 1;
					} ## end if ( ( $hHunk->{lines}...))
				}     ## end for ( my $j = $direction...)
				if ( $all_same > 0 ) {

					# The insertion is right before or after the removal. That's pointless.
					$undos{ $hIncs{$inc}{remove}{lineid} } = 1;
					$hIncs{$inc}{applied}                  = 1;
					$hIncs{$inc}{insert}{spliceme}         = 1;
					next;
				} ## end if ($all_same)
			}     ## end if ( ( $hIncs{$inc}{insert...}))

			# c) Move somewhere else, or change include type. Can't be anything else here.
			if ( $hIncs{$inc}{elogind}{hunkid} > -1 ) {

				# Just undo the removal of the elogind insert.
				my $hId                                          = $hIncs{$inc}{elogind}{hunkid};
				my $lId                                          = $hIncs{$inc}{elogind}{lineid};
				substr( $hFile{hunks}[$hId]{lines}[$lId], 0, 1 ) = " ";
			} elsif ( $hIncs{$inc}{insert}{elogind} ) {

				# Do not move masked includes under our block.
				$undos{ $hIncs{$inc}{remove}{lineid} } = 1;
				$hIncs{$inc}{insert}{spliceme}         = 1;
			}

			$hIncs{$inc}{applied} = 1;
			next;
		} ## End of ruleset 1

		# === Ruleset 2 : Handling of insertions, not handled by 1          ===
		# =====================================================================
		if ( $$line =~ m,^\+\s*#include\s+[<"']([^>"']+)[>"'], ) {
			$hIncs{$1}{applied} and next; ## No double handling

			# Pre: Sanity check:
			defined( $hIncs{$1}{insert}{hunkid} ) and $hIncs{$1}{insert}{hunkid} > -1
			or return hunk_failed( "check_includes: Unrecorded insertion found!" );

			# Nicely enough we are already set here.
			$hIncs{$1}{applied} = 1;

			next;
		} ## end if ( $$line =~ m,^\+\s*#include\s+[<"']([^>"']+)[>"'],)

		# === Ruleset 3 : Handling of "needed by elogind" blocks            ===
		# =====================================================================
		if ( $in_elogind_block
		     && ( $$line =~ m,^-\s*#include\s+[<"']([^>"']+)[>"'], ) ) {
			$hIncs{$1}{applied} and next; ## No double handling

			# Pre: Sanity check:
			defined( $hIncs{$1}{elogind}{hunkid} ) and $hIncs{$1}{elogind}{hunkid} > -1
			or return hunk_failed( "check_includes: Unrecorded elogind include found!" );

			# As 1 and 2 do not apply, simply undo the removal.
			substr( $$line, 0, 1 ) = " ";
			$hIncs{$1}{applied}    = 1;

			next;
		} ## end if ( $in_elogind_block...)

		# === Other 1 : Look for "needed by elogind" block starts           ===
		# =====================================================================
		if ( $$line =~ m,^[- ]\s*//+.*needed\s+(?:by|for)\s+elogind.*,i ) {
			$in_elogind_block = 1;

			# Never remove the block start
			( $$line =~ m,^-, ) and substr( $$line, 0, 1 ) = " ";

			# While we are here, we can see to it, that the additional empty
			# line above our marker does not get removed:
			( $i > 0 )
			and ( $hHunk->{lines}[ $i - 1 ] =~ m/^-\s*$/ )
			and substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = " ";

			next;
		} ## end if ( $$line =~ m,^[- ]\s*//+.*needed\s+(?:by|for)\s+elogind.*,i)

		# === Other 2 : elogind include blocks end, when the first line is  ===
		# ===           found that does not starts with #include            ===
		# ===
		# =====================================================================
		if ( $in_elogind_block && !( $$line =~ m,^.\s*#include$, ) ) {

			# diff may want to remove the first empty line after our block.
			( $$line =~ m,^-\s*$, ) and substr( $$line, 0, 1 ) = " ";

			# Done now...
			$in_elogind_block = 0;
		}

		# === Other 3 : Undo all other removals in elogind include blocks   ===
		# =====================================================================
		$in_elogind_block and ( $$line =~ m,^-, ) and substr( $$line, 0, 1 ) = " ";

		# Note: Although it looks like all rules are out the window here, all
		#       elogind includes that are handled above, end in a 'next', so
		#       those won't reach here. Actually 'Other 3' would be never
		#       reached with an #include line.

	} ## End of looping lines

	# Before we can leave, we have to neutralize the %undo lines:
	for my $lId ( keys %undos ) {
		substr( $hHunk->{lines}[$lId], 0, 1 ) = " ";
	}

	return 1;
} ## end sub check_includes

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

	# Early exits:
	defined( $hHunk ) or die( "check_masks: hHunk is undef" );
	$hHunk->{useful} or die( "check_masks: Nothing done but hHunk is useless?" );

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

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Entering an elogind mask
		# ---------------------------------------
		if ( is_mask_start( $$line ) ) {
			$in_mask_block and return hunk_failed( "check_masks: Mask start found while being in a mask block!" );
			$in_insert_block
			and return hunk_failed( "check_masks: Mask start found while being in an insert block!" );
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_insert_block       = 0;
			$in_mask_block         = 1;
			$mask_block_start      = $i;
			$mask_end_line         = -1;
			$move_to_line          = -1;

			# While we are here we can check the previous line.
			# All masks shall be preceded by an empty line to enhance readability.
			# So any attempt to remove them must be stopped.
			( $i > 0 )
			and ( $hHunk->{lines}[ $i - 1 ] =~ m/^-\s*$/ )
			and substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = " ";

			next;
		} ## end if ( is_mask_start($$line...))

		# Entering an elogind insert
		# ---------------------------------------
		if ( is_insert_start( $$line ) ) {
			$in_mask_block and return hunk_failed( "check_masks: Insert start found while being in a mask block!" );
			$in_insert_block and return hunk_failed( "check_masks: Insert start found while being in an insert block!" );
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_insert_block       = 1;
			$in_mask_block         = 0;
			$mask_block_start      = -1;
			$mask_end_line         = -1;
			$move_to_line          = $i;

			# While we are here we can check the previous line.
			# All inserts shall be preceded by an empty line to enhance readability.
			# So any attempt to remove them must be stopped.
			( $i > 0 )
			and ( $hHunk->{lines}[ $i - 1 ] =~ m/^-\s*$/ )
			and substr( $hHunk->{lines}[ $i - 1 ], 0, 1 ) = " ";

			next;
		} ## end if ( is_insert_start($$line...))

		# Count regular #if
		$$line =~ m/^-#if/ and ++$regular_ifs;

		# Switching from Mask to else.
		# Note: Inserts have no #else, they make no sense.
		# ---------------------------------------
		if ( is_mask_else( $$line ) ) {
			$in_mask_block
			or return hunk_failed( "check_masks: Mask else found outside any mask block!" );

			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_else_block         = 1;
			$move_to_line          = $i;
			next;
		} ## end if ( $in_mask_block &&...)

		# Ending a Mask block
		# ---------------------------------------
		if ( is_mask_end( $$line ) ) {
			$in_mask_block or return hunk_failed( "check_masks: #endif // 0 found outside any mask block" );
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_mask_block         = 0;
			$in_else_block         = 0;
			$mask_block_start      = -1;
			$mask_end_line         = $i;
			next;
		} ## end if ( is_mask_end($$line...))

		# Ending an insert block
		# ---------------------------------------
		if ( is_insert_end( $$line ) ) {
			$in_insert_block or return hunk_failed( "check_masks: #endif // 1 found outside any insert block" );
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_insert_block       = 0;
			$mask_block_start      = -1;
			$mask_end_line         = $i;
			next;
		} ## end if ( is_insert_end($$line...))

		# End regular #if
		$$line =~ m/^-#endif/ and --$regular_ifs;

		# Special treatment for all mask-else and insert blocks.
		# (Well, that's what this function is all about, isn't it?)
		if ( $in_insert_block || ( $in_mask_block && $in_else_block ) ) {
			# Remove '-' prefixes in all lines within insert and mask-else blocks
			# -------------------------------------------------------------------
			if ( $$line =~ m,^-, ) {
				substr( $$line, 0, 1 ) = " "; ## Remove '-'
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
					substr( $cpy_line, 0, 1 ) = "+"; ## Above, this is an addition.
					splice( @{ $hHunk->{lines} }, $move_to_line++, 0, $cpy_line );
					$hHunk->{count} += 1;
					$i++; ## We have to advance i, or the next iteration puts as back here.
				}

				# Case 1 ; The addition: move the offending line back above the else/insert
				# -----------------------------------------------------------------------
				else {
					splice( @{ $hHunk->{lines} }, $i, 1 ); ## Order matters here.
					splice( @{ $hHunk->{lines} }, $move_to_line++, 0, $cpy_line );

					# Note: No change to $hHunk->{count} here, as the lines are moved.
				} ## end if ( ( $mask_end_line ...))

				# No matter whether we have copied or moved, the if/else moved down.
				$mask_end_line > -1 and ++$mask_end_line or ++$mask_block_start;

				next;
			}
		}

		# Being here means that we are in a mask block or outside of any block.
		# A special thing to consider is when diff wants to change the end or
		# add something to the end of a mask block, or right before an insertion
		# block.
		# As our blocks are getting removed by diff, the addition will happen
		# right after that. So anything added the very next lines after we have
		# exited our domain must be moved up.
		if ( 0 == $in_mask_block ) {
			if ( ( $move_to_line > -1 ) && ( $$line =~ m,^\+, ) ) {
				my $cpy_line = $$line;
				splice( @{ $hHunk->{lines} }, $i, 1 ); ## Order matters here.
				splice( @{ $hHunk->{lines} }, $move_to_line++, 0, $cpy_line );

				# Note: Again no change to $hHunk->{count} here, as the lines are moved.
				next;
			}

			# End our mask block ending awareness at the first non-insertion line after a mask block.
			# ---------------------------------------------------------------------------------------
			$mask_end_line = -1;
			$move_to_line  = -1;
		}
	} ## End of looping lines

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

	# Early exits:
	defined( $hHunk ) or return 0;
	$hHunk->{useful} or return 0;

	# Count non-elogind block #ifs. This is needed, so normal
	# #if/#else/#/endif constructs can be put inside both the original
	# and the alternative block.
	my $regular_ifs = 0;

	# Remember the final mask state for later reversal
	# ------------------------------------------------
	my $hunk_ends_in_mask                     = $in_mask_block;
	my $hunk_ends_in_else                     = $in_else_block;
	$in_else_block                            = 0;
	$hHunk->{masked_start} and $in_mask_block = 1 or $in_mask_block = 0;

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# The increment/decrement variant can cause negative values:
		$in_mask_block < 0 and $in_mask_block = 0;
		$in_else_block < 0 and $in_else_block = 0;

		# Quick mask checks, we must have the intermediate states
		# -------------------------------------------------------
		is_mask_start( $$line ) and ++$in_mask_block and next;
		if ( is_mask_end( $$line ) ) {
			$in_mask_block--;
			$in_else_block--;
			next;
		}

		# Entering a __GLIBC__ block as mask
		# ---------------------------------------
		if ( $$line =~ m/^-#if(?:def|\s+defined).+__GLIBC__/ ) {
			## Note: Here it is perfectly fine to be in an elogind mask block.
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_glibc_block        = 1;
			next;
		} ## end if ( $$line =~ m/^-#if(?:def|\s+defined).+__GLIBC__/)

		# Entering a __GLIBC__ block as insert
		# ---------------------------------------
		if ( $$line =~ m/^-#if(?:ndef|\s+!defined).+__GLIBC__/ ) {
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_glibc_block        = 1;
			$in_else_block++;
			next;
		} ## end if ( $$line =~ m/^-#if(?:ndef|\s+!defined).+__GLIBC__/)

		# Count regular #if
		$$line =~ m/^-#if/ and ++$regular_ifs;

		# Switching from __GLIBC__ to else
		# ---------------------------------------
		if ( $$line =~ m,^[- ]?#else\s+[/]+\s+__GLIBC__, ) {
			++$in_else_block;
			substr( $$line, 0, 1 ) = " ";
			next;
		}

		# Ending a __GLBC__ block
		# ---------------------------------------
		if ( $$line =~ m,^-#endif\s*///?.*__GLIBC__, ) {
			( !$in_glibc_block )
			and return hunk_failed( "check_musl: #endif // __GLIBC__ found outside any __GLIBC__ block" );
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
			$in_glibc_block        = 0;
			$in_else_block--;
			next;
		} ## end if ( $$line =~ m,^-#endif\s*///?.*__GLIBC__,)

		# End regular #if
		$$line =~ m/^-#endif/ and --$regular_ifs;

		# Remove '-' prefixes in all lines within the musl (#else) blocks
		# -------------------------------------------------------------------
		if ( ( $$line =~ m,^-, )
		     && ( $in_glibc_block > 0 )
		     && ( $in_else_block > $in_mask_block ) ) {
			substr( $$line, 0, 1 ) = " "; ## Remove '-'
		}                                 ## end if ( ( $$line =~ m,^-,...))
	}                                     ## End of looping lines

	# Revert the final mask state remembered above
	# ------------------------------------------------
	$in_mask_block = $hunk_ends_in_mask;
	$in_else_block = $hunk_ends_in_else;

	return 1;
} ## end sub check_musl

# -----------------------------------------------------------------------
# --- Check for attempts to revert 'elogind' to 'systemd'             ---
# --- Note: We only check for single line reverts like:               ---
# --- |-  // This is how elogind does it                              ---
# --- |+  // This is how systemd does it                              ---
# -----------------------------------------------------------------------
sub check_name_reverts {

	# Early exits:
	defined( $hHunk ) or return 0;
	$hHunk->{useful} or return 0;

	# Note down what is changed, so we can have inline updates
	my %hRemovals = (); ## {string}{line}     = line_no
	##         {masked}   = 1 in mask block, 0 not masked or in else block
	##         {spliceme} = 1 for splicing, 0 otherwise


	# Remember the final mask state for later reversal
	# ------------------------------------------------
	my $hunk_ends_in_mask                     = $in_mask_block;
	my $hunk_ends_in_else                     = $in_else_block;
	$in_else_block                            = 0;
	$hHunk->{masked_start} and $in_mask_block = 1 or $in_mask_block = 0;

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		defined( $$line )
		or return hunk_failed( "check_name_reverts: Line " . ( $i + 1 ) . "/$hHunk->{count} is undef?" );

		# The increment/decrement variant can cause negative values:
		$in_mask_block < 0 and $in_mask_block = 0;
		$in_else_block < 0 and $in_else_block = 0;

		# Quick mask checks, we must have the intermediate states
		# -------------------------------------------------------
		is_mask_start( $$line ) and ++$in_mask_block and next;
		is_mask_else( $$line ) and ++$in_else_block and next;
		if ( is_mask_end( $$line ) ) {
			$in_mask_block = 0;
			$in_else_block = 0;
			next;
		}
		my $is_masked_now = ( ( $in_mask_block > 0 ) && ( 1 < $in_else_block ) ) ? 1 : 0;

		# Note down removals
		# ---------------------------------
		if ( $$line =~ m/^[- ][#\/* ]*\s*(.*elogind.*)\s*[*\/ ]*$/ ) {
			# printf("Noting down removal %d: \"%s\"\n", $i, $1);
			# Note it down for later:
			$hRemovals{$1} = { line => $i,, masked => $is_masked_now, spliceme => 0 };
			next;
		}

		# Check Additions
		# ---------------------------------
		if ( $$line =~ m/^\+[#\/* ]*\s*(.*systemd.*)\s*[*\/ ]*$/ ) {
			my $replace_text = $1;

			# printf("Noting down addition %d: \"%s\"\n", $i, $1);

			# There is some specialities:
			# =============================================================
			# 1) References to the systemd github or .io site must not be changed,
			#    unless it is a reference to the issues tracker.
			$replace_text =~ m,github\.com/systemd,
			and ( !( $replace_text =~ m,/issues, ) )
			and next;
			$replace_text =~ m,systemd\.io, and next;

			# 2) /run/systemd/ must not be changed, as other applications
			#    rely on that naming.
			# Note: The /run/elogind.pid file is not touched by that, as
			#       systemd does not have something like that.
			$replace_text =~ m,/run/systemd, and next;

			# 3) Several systemd website urls must not be changed, too
			for my $pat ( keys %SYSTEMD_URLS ) {
				$replace_text =~ m/$pat/ and next;
			}

			# 4) To be a dropin-replacement, we also need to not change any org[./]freedesktop[./]systemd strings
			$replace_text =~ m,/?org[./]freedesktop[./]systemd, and next;

			# 5) Do not replace referrals to systemd[1]
			$replace_text =~ m,systemd\[1\], and next;

			# 6) References to systemd-homed and other tools not shipped by elogind
			#    must not be changed either, or users might think elogind has its
			#    own replacements.
			my $is_wrong_replace = ( ( $replace_text =~ m,systemd[-_](home|import|journal|network|oom|passwor|udev)d, ) ||
			                         ( $replace_text =~ m,systemd[-_](analyze|creds|cryptsetup|firstboot|home|nspawn|repart|syscfg|sysusers|tmpfiles|devel/), ) )
			                       ? 1 : 0;

			# We have to differentiate between simple systemd, longer systemd-logind and man page volume numbers
			my $our_text_long  = $replace_text;
			my $our_text_short = $our_text_long;
			$our_text_long =~ s/systemd[-_]logind/elogind/g;
			$our_text_short =~ s/systemd/elogind/g;
			$our_text_long eq $replace_text and $our_text_long =~ s/systemd-stable/elogind/g; # Alternative if systemd-logind does not match
			my $our_text_man_page = $our_text_short;
			$our_text_man_page =~ s,<manvolnum>1</manvolnum>,<manvolnum>8</manvolnum>,;

			# Make the following easier with a simple shortcut:
			my $o_txt =
				defined( $hRemovals{$our_text_long} ) ? $our_text_long :
				defined( $hRemovals{$our_text_short} ) ? $our_text_short :
				defined( $hRemovals{$our_text_man_page} ) ? $our_text_man_page :
				"";
			# If we had this text removed, $o_txt is now the removed version of this addition

			# printf("Got o_txt %d: \"%s\"\n", $i, $o_txt);
			# --- Case A) If we accidentally renamed a systemd-only tool to elogind-<foo>,  ---
			# ---         although we do not ship it, do not deny the reversal.             ---
			# ---------------------------------------------------------------------------------

			if ( 1 == $is_wrong_replace ) {
				( 0 < length( $o_txt ) ) and $hProtected{$$line} = 1 and next;

				# However, if the patch wants to _add_ a reference to a tool we do not ship, splice it away
				$hRemovals{$replace_text}{spliceme} = $i;

				# If this is followed by an empty line addition, splice that, too
				( $i < ( $hHunk->{count} - 1 ) ) and
				( $hHunk->{lines}[$i + 1] =~ m,^\+[#]*\s*[*/]*\s*$, ) and
				$hRemovals{$replace_text . "_blank"}{masked}   = $is_masked_now;
				$hRemovals{$replace_text . "_blank"}{spliceme} = $i + 1;
			}

			# --- Case B) If this is a simple switch, or a move from non-masked to masked, undo it. ---
			# -----------------------------------------------------------------------------------------
			if ( ( 0 < length( $o_txt ) ) && (
				( $hRemovals{$o_txt}{line} < $i ) ||
				( $is_masked_now && ( $hRemovals{$o_txt}{masked} < 1 ) )
			) ) {
				substr( $hHunk->{lines}[ $hRemovals{$o_txt}{line} ], 0, 1 ) = " ";
				$hRemovals{$o_txt}{spliceme}                                = $i; ## Splice the addition
				# printf("Undo %d and splice %d\n", $hRemovals{$o_txt}{line}, $i);
				next;
			}

			# --- Case C) Otherwise replace the addition with our text, if we have one. ---
			# -----------------------------------------------------------------------------
			if ( $our_text_short ne $our_text_man_page ) {
				# printf( "\nReplacing (man)\n\t'%s' with\n\t'%s'\n\t\t\t", $replace_text, $our_text_man_page );
				$$line =~ s,systemd,elogind,g;
				$$line =~ s,<manvolnum>1</manvolnum>,<manvolnum>8</manvolnum>,;
			} elsif ( $replace_text ne $our_text_long ) {
				# printf( "\nReplacing (long)\n\t'%s' with\n\t'%s'\n\t\t\t", $replace_text, $our_text_long );
				$replace_text =~ m/systemd-stable/
				and $$line =~ s,systemd-stable,elogind,g
				or $$line =~ s,systemd-logind,elogind,g;
			} elsif ( $replace_text ne $our_text_short ) {
				# printf( "\nReplacing (short)\n\t'%s' with\n\t'%s'\n\t\t\t", $replace_text, $our_text_short );
				$$line =~ s,systemd,elogind,g;
			} else {
				print "\nERROR: This does not make sense:\n";
				printf( "\treplace_text     : '%s'\n", $replace_text );
				printf( "\tour_text_short   : '%s'\n", $our_text_short );
				printf( "\tour_text_long    : '%s'\n", $our_text_long );
				printf( "\tour_text_man_page: '%s'\n", $our_text_man_page );
				exit 1;
			}

			# In some meson files, we need the variable "systemd_headers".
			# This refers to the systemd API headers that get installed,
			# and must therefore not be renamed to elogind_headers.
			$$line =~ s/elogind_headers/systemd_headers/g;

			# systemd-sleep.conf is *not* elogind-sleep.conf, but just sleep.conf in elogind
			$$line =~ s/(?:systemd|elogind)-(sleep\.conf)/$1/;
			# printf("Final line: '%s'\n", $$line);
		} ## end if ( $$line =~ m/^\+[# ]*\s*(.*systemd.*)\s*$/)
	}     ## end for ( my $i = 0 ; $i < ...)

	# Splice the lines that were noted for splicing
	# ------------------------------------------------
	my %hSplices = ();
	for my $k ( keys %hRemovals ) {
		$hRemovals{$k}{spliceme} or next;
		$hSplices{ $hRemovals{$k}{spliceme} } = 1;
		# printf("Splice line %d", $hRemovals{$k}{spliceme});
	}
	for my $l ( sort { $b <=> $a } keys %hSplices ) {
		splice( @{ $hHunk->{lines} }, $l, 1 );
		--$hHunk->{count};
	}

	# Revert the final mask state remembered above
	# ------------------------------------------------
	$in_mask_block = $hunk_ends_in_mask;
	$in_else_block = $hunk_ends_in_else;

	return 1;
} ## end sub check_name_reverts

# -----------------------------------------------------------------------
# --- Check for attempts to uncomment unsupported API functions       ---
# --- in .sym files.                                                  ---
# --- In here we change unsupported function calls from               ---
# ---        sd_foo_func;                                             ---
# --- to                                                              ---
# ---        /* sd_foo_func; */                                       ---
# -----------------------------------------------------------------------
sub check_sym_lines {

	# Early exits:
	defined( $hHunk ) or return 0;
	$hHunk->{useful} or return 0;

	# Only .sym files are handled here
	$hFile{source} =~ m/\.sym\.pwx$/ or return 1;

	# Note down what is changed, so we can have inline updates
	my %hAdditions = ();
	my %hRemovals  = ();

	# We need a sortable line map for possible later splicing
	my %hAddMap = ();

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		defined( $$line )
		or return hunk_failed( "check_sym_files: Line " . ( $i + 1 ) . "/$hHunk->{count} is undef?" );

		# Note down removals
		# ---------------------------------
		if ( $$line =~ m,^-\s*/\*\s+(\S.+;)\s+\*/\s*$, ) {
			$hRemovals{$1}{line} = $i;
			next;
		}

		# Check Additions
		# ---------------------------------
		if ( $$line =~ m,^\+\s*([^ /].+;)\s*$, ) {
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

	# Early exits:
	defined( $hHunk ) or die( "check_useless: hHunk is undef" );
	$hHunk->{useful} or die( "check_useless: Nothing done but hHunk is useless?" );

	# Note down removals, and where they start
	my %hRemovals = ();
	my $r_start   = -1;

	# We later work with an offset, to check for useless changes to splice
	my %hSplices = ();
	my $r_offset = -1;

	# Now go through the line and find out what is to be done
	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# --- (1) Note down removal ---
		if ( $$line =~ m/^-(.*)$/ ) {
			my $token = $1 || "";
			$token =~ s/\s+$//; ## No trailing whitespace/lines!
			$r_start > -1 or $r_start = $i;
			length( $token )
			and $hRemovals{$token}      = $i
			or $hRemovals{"empty" . $i} = $i;
			next;
		}

		# --- (2) Check Addition ---
		if ( $$line =~ m/^\+(.*)$/ ) {
			my $token = $1 || "";
			$token =~ s/\s+$//; ## No trailing whitespace/lines!
			$r_offset > -1 or $r_offset = $i - $r_start;
			if ( ( length( $token ) && ( defined( $hRemovals{$token} ) && ( $hRemovals{$token} + $r_offset ) == $i ) )
			     || ( !length( $token ) && ( defined( $hRemovals{"empty" . ( $i - $r_offset )} ) ) ) ) {
				# Yep, this has to be reverted.
				substr( $hHunk->{lines}[$i - $r_offset], 0, 1 ) = " ";
				$hSplices{$i}                                   = 1;
			}
			next;
		}

		# --- (3) Reset state on the first out-of-block line
		$r_start   = -1;
		$r_offset  = -1;
		%hRemovals = ();
	} ## end for ( my $i = 0 ; $i < ...)

	# Now go through the splice map and splice from back to front
	for my $line_no ( sort { $b <=> $a } keys %hSplices ) {
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
	my ( $commit ) = @_;

	# It is completely in order to not wanting to checkout a specific commit.
	defined( $commit ) and length( $commit ) or return 1;

	my $new_commit = "";
	my $git        = Git::Wrapper->new( $upstream_path );
	my @lOut       = ();

	# Save the previous commit
	try {
		@lOut = $git->rev_parse( { short => 1 }, "HEAD" );
	} catch {
		print "ERROR: Couldn't rev-parse $upstream_path HEAD\n";
		print "Exit Code : " . $_->status . "\n";
		print "Message   : " . $_->error . "\n";
		return 0;
	};
	$previous_commit = $lOut[0];

	# Get the shortened commit hash of $commit
	try {
		@lOut = $git->rev_parse( { short => 1 }, $commit );
	} catch {
		print "ERROR: Couldn't rev-parse $upstream_path \"$commit\"\n";
		print "Exit Code : " . $_->status . "\n";
		print "Message   : " . $_->error . "\n";
		return 0;
	};
	$new_commit = $lOut[0];

	# Now check it out, unless we are already there:
	if ( $previous_commit ne $new_commit ) {
		print "Checking out $new_commit in upstream tree...";
		try {
			$git->checkout( $new_commit );
		} catch {
			print "\nERROR: Couldn't checkout \"new_commit\" in $upstream_path\n";
			print "Exit Code : " . $_->status . "\n";
			print "Message   : " . $_->error . "\n";
			return 0;
		};
		print " done\n";
	} ## end if ( $previous_commit ...)

	return 1;
} ## end sub checkout_upstream

# -----------------------------------------------------------------------
# --- Completely clean up the current %hFile data structure.          ---
# -----------------------------------------------------------------------
sub clean_hFile {
	defined( $hFile{count} ) or return 1;

	for ( my $i = $hFile{count} - 1; $i > -1; --$i ) {
		defined( $hFile{hunks}[$i] ) and undef( %{ $hFile{hunks}[$i] } );
	}

	$hFile{count}  = 0;
	$hFile{hunks}  = [];
	$hFile{output} = [];

	return 1;
} ## end sub clean_hFile

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
		`diff -qu "$hFile{source}" "$hFile{target}" 1>/dev/null 2>&1`;
		$? or print "same\n" and return 0;

		# Shell and meson files must be prepared. See prepare_meson()
		$hFile{is_sh} and $hFile{pwxfile} = 1 and prepare_shell;

		# We mask double dashes in XML comments using XML hex entities. These
		# must be unmasked for processing.
		$hFile{is_xml} and $hFile{pwxfile} = 1 and prepare_xml;
	} ## end if ( 0 == $hFile{create...})

	# Let's have three shortcuts:
	my $src = $hFile{source};
	my $tgt = $hFile{target};
	my $prt = $hFile{part};

	# Now the diff can be built ...
	my @lDiff = `diff -N -u "$src" "$tgt"`;

	# ... the head of the output can be generated ...
	@{ $hFile{output} } = splice( @lDiff, 0, 2 );
	chomp $hFile{output}[0];                   # These now have absolute paths, and source meson files have a
	chomp $hFile{output}[1];                   # .pwx extensions. That is not what the result shall look like.
	$hFile{create}                             # But we have $hFile{part}, which is already the
	and $hFile{output}[0] =~ s,$src,/dev/null, # relative file name of the file we are
	or $hFile{output}[0] =~ s,$src,a/$prt,;    # processing, and we know if a file is
	$hFile{output}[1] =~ s,$tgt,b/$prt,;       # to be created.

	# ... and the raw hunks can be stored.
	for ( my $line_no = 1; $line_no < scalar @lDiff; ++$line_no ) {
		( '@@' eq substr( $lDiff[$line_no], 0, 2 ) )
		and ( build_hHunk( splice( @lDiff, 0, $line_no )) or return 0 )
		and $line_no = 0;
	}
	scalar @lDiff and build_hHunk( @lDiff );

	return 1;
} ## end sub diff_hFile

# -----------------------------------------------------------------------
# --- Finds all relevant files and store them in @wanted_files        ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub generate_file_list {

	# Do some cleanup first. Just to be sure.
	`rm -rf build`;
	`find -iname '*.orig' -or -iname '*.bak' -or -iname '*.rej' -or -iname '*~' -or -iname '*.gc??' | xargs rm -f`;

	# Build wanted files hash
	while ( my $want              = shift @wanted_files ) {
		$have_wanted              = 1;
		$want =~ m,^\./, or $want = "./$want";
		$hWanted{$want}           = 1;
		$want =~ s/elogind/systemd/g;
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
		$hWanted{$xFile} == 2 and next; ## Already handled or unavailable
		find( \&wanted, "$xFile" );
	} ## end for my $xFile ( keys %hWanted)

	# All files that shall be created must be added manually now.
	scalar keys %hToCreate and push @source_files, keys %hToCreate;

	# Just to be sure...
	scalar @source_files
	or print( "ERROR: No source files found? Where the hell are we?\n" )
	   and return 0;

	# Get the maximum file length and build $file_fmt
	my $mlen = 0;
	for my $f ( @source_files ) {
		length( $f ) > $mlen and $mlen = length( $f );
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
	my ( $offset ) = @_;

	my $src_len   = 0;
	my $tgt_len   = 0;
	my $lCount    = $hHunk->{count};
	my $src_start = $hHunk->{src_start};
	my $tgt_start = defined( $offset ) ? $src_start + $$offset : $hHunk->{tgt_start};

	for ( my $i = 0; $i < $lCount; ++$i ) {
		if ( $hHunk->{lines}[$i] =~ m/^\+/ ) {
			$tgt_len++;
		} elsif ( $hHunk->{lines}[$i] =~ m/^\-/ ) {
			$src_len++;
		} else {
			$src_len++;
			$tgt_len++;
		}
	} ## end for ( my $i = 0 ; $i < ...)

	# If an offset reference was given, add back the size diff
	defined( $offset )
	and $$offset += $tgt_len - $src_len;

	return sprintf( "%s -%d,%d +%d,%d %s", '@@', $src_start, $src_len, $tgt_start, $tgt_len, '@@' );
} ## end sub get_hunk_head

# -----------------------------------------------------------------------
# --- Whenever a check finds an illegal situation, it has to call     ---
# --- this subroutine which terminates the progress line and creaes   ---
# --- an entry in @lFails.                                            ---
# --- Param: An error message, preferably with the name of the failed ---
# ---        check.                                                   ---
# --- Return: Always zero.                                            ---
# -----------------------------------------------------------------------
sub hunk_failed {
	my ( $msg ) = @_;
	my $num     = scalar @lFails;

	# Generate entry:
	push @lFails, {
		hunk => [ get_hunk_head ],
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
		part => $hFile{part} };

	# Add the hunk itself
	for my $line ( @{ $hHunk->{lines} } ) {
		push @{ $lFails[$num]{hunk} }, $line;
	}

	# And terminate the progress line:
	print "$msg\n";

	return 0;
} ## end sub hunk_failed

# -----------------------------------------------------------------------
# --- Check the current $hHunk whether it still does anything.        ---
# --- While being at it, prune it to what a diff needs:               ---
# ---   3 lines before the first and 3 lines after the last change.   ---
# --- Returns 1 if at least one change was found, 0 otherwise.        ---
# -----------------------------------------------------------------------
sub hunk_is_useful {

	# Early exits:
	defined( $hHunk ) or return 0;
	$hHunk->{useful} or return 0;

	# Go through the lines and see whether we have any changes
	$hHunk->{useful} = 0;

	for ( my $i = 0; $i < $hHunk->{count}; ++$i ) {
		if ( $hHunk->{lines}[$i] =~ m/^[-+]/ ) {
			$hHunk->{useful} = 1;
			return 1;
		}
	} ## end for ( my $i = 0 ; $i < ...)

	return 0;
} ## end sub hunk_is_useful

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any insertion end ---
# --------------------------------------------------------------
sub is_insert_end {
	my ( $line ) = @_;

	defined( $line ) and length( $line ) or return 0;

	if ( ( $line =~ m,^[- ]?#endif\s*/(?:[*/]+)\s*1, )
	     || ( $line =~ m,//\s+1\s+-->\s*$, )
	     || ( $line =~ m,\*\s+//\s+1\s+\*\*/\s*$, ) ) {
		return 1;
	} ## end if ( ( $line =~ m,^[- ]?#endif\s*/(?:[*/]+)\s*1,...))

	return 0;
} ## end sub is_insert_end

# ----------------------------------------------------------------
# --- Return 1 if the argument consists of any insertion start ---
# ----------------------------------------------------------------
sub is_insert_start {
	my ( $line ) = @_;

	defined( $line ) and length( $line ) or return 0;

	if ( ( $line =~ m/^[- ]?#if\s+1.+elogind/ )
	     || ( $line =~ m/<!--\s+1.+elogind.+-->\s*$/ ) ) {
		return 1;
	}

	return 0;
} ## end sub is_insert_start

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any mask else     ---
# --------------------------------------------------------------
sub is_mask_else {
	my ( $line ) = @_;

	defined( $line ) and length( $line ) or return 0;

	if ( ( $line =~ m,^[- ]?#else\s+[/]+\s+0, )
	     || ( $line =~ m,else\s+[/]+\s+0\s+-->\s*$, )
	     || ( $line =~ m,\*\s+else\s+[/]+\s+0\s+\*\*/\s*$, ) ) {
		return 1;
	} ## end if ( ( $line =~ m/^[- ]?#else/...))

	return 0;
} ## end sub is_mask_else

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any mask end      ---
# --------------------------------------------------------------
sub is_mask_end {
	my ( $line ) = @_;

	defined( $line ) and length( $line ) or return 0;

	if ( ( $line =~ m,^[- ]?#endif\s*/(?:[*/]+)\s*(?:0), )
	     || ( $line =~ m,//\s+0\s+-->\s*$, )
	     || ( $line =~ m,\*\s+//\s+0\s+\*\*/\s*$, ) ) {
		return 1;
	} ## end if ( ( $line =~ m,^[- ]?#endif\s*/(?:[*/]+)\s*(?:0),...))

	return 0;
} ## end sub is_mask_end

# --------------------------------------------------------------
# --- Return 1 if the argument consists of any mask start    ---
# --------------------------------------------------------------
sub is_mask_start {
	my ( $line ) = @_;

	defined( $line ) and length( $line ) or return 0;

	if (
		( $line =~ m/^[- ]?#if\s+0.+elogind/ )
		|| ( ( $line =~ m/<!--\s+0.+elogind/ )
		     && !( $line =~ m/-->\s*$/ ) )
		|| ( ( $line =~ m,/\*\*\s+0.+elogind, )
		     && !( $line =~ m,\*\*/\s*$, ) ) ) {
		return 1;
	} ## end if ( ( $line =~ m/^[- ]?#if\s+0.+elogind/...))

	return 0;
} ## end sub is_mask_start

# -----------------------------------------------------------------------
# --- parse the given list for arguments.                             ---
# --- returns 1 on success, 0 otherwise.                              ---
# --- sets global $show_help to 1 if the long help should be printed. ---
# -----------------------------------------------------------------------
sub parse_args {
	my @args   = @_;
	my $result = 1;

	for ( my $i = 0; $i < @args; ++$i ) {

		# Check for -c|--commit option
		# -------------------------------------------------------------------------------
		if ( $args[$i] =~ m/^-(?:c|-commit)$/ ) {
			if ( ( ( $i + 1 ) >= @args )
			     || ( $args[ $i + 1 ] =~ m,^[-/.], ) ) {
				print "ERROR: Option $args[$i] needs a refid as argument!\n\nUsage: $USAGE_SHORT\n";
				$result = 0;
				next;
			} ## end if ( ( ( $i + 1 ) >= @args...))
			$wanted_commit = $args[ ++$i ];
		} ## end if ( $args[$i] =~ m/^-(?:c|-commit)$/)

		# Check for --create option
		# -------------------------------------------------------------------------------
		elsif ( $args[$i] =~ m/^--create$/ ) {
			$do_create = 1;
		}

		# Check for -f|--file option
		# -------------------------------------------------------------------------------
		elsif ( $args[$i] =~ m/^-(?:f|-file)$/ ) {
			if ( ( ( $i + 1 ) >= @args )
			     || ( $args[ $i + 1 ] =~ m,^[-], ) ) {
				print "ERROR: Option $args[$i] needs a path as argument!\n\nUsage: $USAGE_SHORT\n";
				$result = 0;
				next;
			} ## end if ( ( ( $i + 1 ) >= @args...))
			push @wanted_files, split( /,/, $args[ ++$i ] );
		} ## end elsif ( $args[$i] =~ m/^-(?:f|-file)$/)

		# Check for -h|--help option
		# -------------------------------------------------------------------------------
		elsif ( $args[$i] =~ m/^-(?:h|-help)$/ ) {
			$show_help = 1;
		}

		# Check for --stay option
		# -------------------------------------------------------------------------------
		elsif ( $args[$i] =~ m/^--stay$/ ) {
			$do_stay = 1;
		}

		# Check for unknown options:
		# -------------------------------------------------------------------------------
		elsif ( $args[$i] =~ m/^-/ ) {
			print "ERROR: Unknown option \"$args[$1]\" encountered!\n\nUsage: $USAGE_SHORT\n";
			$result = 0;
		}

		# Everything else is considered to the path to upstream
		# -------------------------------------------------------------------------------
		else {
			# But only if it is not set, yet:
			if ( length( $upstream_path ) ) {
				print "ERROR: Superfluous upstream path \"$args[$i]\" found!\n\nUsage: $USAGE_SHORT\n";
				$result = 0;
				next;
			}
			if ( !-d "$args[$i]" ) {
				print "ERROR: Upstream path \"$args[$i]\" does not exist!\n\nUsage: $USAGE_SHORT\n";
				$result = 0;
				next;
			}
			$upstream_path = $args[$i];
		} ## end else [ if ( $args[$i] =~ m/^-(?:c|-commit)$/)]
	}     ## End looping arguments

	# If we have no upstream path now, show short help.
	if ( $result && !$show_help && !length( $upstream_path ) ) {
		print "ERROR: Please provide a path to upstream!\n\nUsage: $USAGE_SHORT\n";
		$result = 0;
	}

	# If --create was given, @wanted_files must not be empty
	if ( $result && !$show_help && $do_create && ( 0 == scalar @wanted_files ) ) {
		print "ERROR: --create must not be used on the full tree!\n";
		print "       Add at least one file using the --file option.\n";
		$result = 0;
	}

	# If --stay was given, $wanted_commit must not be empty
	if ( $result && !$show_help && $do_stay && ( 0 == length( $wanted_commit ) ) ) {
		print "ERROR: --stay makes only sense with the -c|--commit option!\n";
		$result = 0;
	}

	# If any of the wanted files do not exist, error out unless --create was used.
	if ( $result && !$show_help && defined( $wanted_files[0] ) ) {
		foreach my $f ( @wanted_files ) {
			-f $f
			or $do_create and $hToCreate{$f}                   = 1
			or print "ERROR: $f does not exist!\n" and $result = 0;
		}
	} ## end if ( $result && !$show_help...)

	return $result;
} ## parse_srgs() end

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
	my $out  = $in . ".pwx";
	my @lIn  = ();
	my @lOut = ();

	# Leech the source file
	if ( open( my $fIn, "<", $in ) ) {
		@lIn = <$fIn>;
		close( $fIn );
	} else {
		die( "$in can not be opened for reading! [$!]" );
	}

	# Now prepare the output, line by line.
	my $is_block = 0;
	my $is_else  = 0;
	my $line_no  = 0;
	for my $line ( @lIn ) {

		chomp $line;
		++$line_no;

		if ( is_mask_start( $line ) ) {
			if ( $is_block > 0 ) {
				print "ERROR: $in:$line_no : Mask start in mask!\n";
				die( "Illegal file" );
			}
			$is_block = 1;
		} elsif ( is_mask_else( $line ) ) {
			if ( 0 == $is_block ) {
				print "ERROR: $in:$line_no : Mask else outside mask!\n";
				die( "Illegal file" );
			}
			$is_else = 1;
		} elsif ( is_mask_end( $line ) ) {
			if ( 0 == $is_block ) {
				print "ERROR: $in:$line_no : Mask end outside mask!\n";
				die( "Illegal file" );
			}
			$is_block = 0;
			$is_else  = 0;
		} elsif ( $is_block && !$is_else ) {
			$line =~ s,^#\s?,,;
			$line =~ s,^\s\s\*\s?,,;
		}

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open( my $fOut, ">", $out ) ) {
		for my $line ( @lOut ) {
			print $fOut "$line\n";
		}
		close( $fOut );
	} else {
		die( "$out can not be opened for writing! [$!]" );
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
		close( $fIn );
	} else {
		die( "$in can not be opened for reading! [$!]" );
	}

	# Now prepare the output, line by line.
	my $is_block = 0;
	my $is_else  = 0;
	my $line_no  = 0;
	for my $line ( @lIn ) {

		chomp $line;
		++$line_no;

		if ( is_mask_start( $line ) ) {
			if ( $is_block > 0 ) {
				print "ERROR: $in:$line_no : Mask start in mask!\n";
				die( "Illegal file" );
			}
			$is_block = 1;
		} elsif ( is_mask_else( $line ) ) {
			if ( 0 == $is_block ) {
				print "ERROR: $in:$line_no : Mask else outside mask!\n";
				die( "Illegal file" );
			}
			$is_else = 1;
		} elsif ( is_mask_end( $line ) ) {
			if ( 0 == $is_block ) {
				print "ERROR: $in:$line_no : Mask end outside mask!\n";
				die( "Illegal file" );
			}
			$is_block = 0;
			$is_else  = 0;
		} elsif ( $is_block && !$is_else ) {
			$line =~ s/&#x2D;/-/g;
		}

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open( my $fOut, ">", $out ) ) {
		for my $line ( @lOut ) {
			print $fOut "$line\n";
		}
		close( $fOut );
	} else {
		die( "$out can not be opened for writing! [$!]" );
	}

	# The temporary file is our new source
	$hFile{source} = $out;

	return 1;
} ## end sub prepare_xml

# -----------------------------------------------------------------------
# --- Special function to not let diff add unwanted or remove our     ---
# --- lines in logind.conf.in (See Issue #2)                          ---
# -----------------------------------------------------------------------
sub protect_config {

	# Early exits:
	defined( $hHunk ) or die( "check_masks: hHunk is undef" );
	$hHunk->{useful} or die( "check_masks: Nothing done but hHunk is useless?" );

	my $is_sleep_block = 0;

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = \$hHunk->{lines}[$i]; ## Shortcut

		# Kill addition of lines we do not need
		# ---------------------------------------
		if ( $$line =~ m,^\+[#]?(?:NAutoVTs|ReserveVT), ) {
			splice( @{ $hHunk->{lines} }, $i--, 1 );
			--$hHunk->{count};
			next;
		}

		# Enter elogind specific [Sleep] block
		# ------------------------------------------
		if ( $$line =~ m,^\-\[Sleep\], ) {
			substr( $$line, 0, 1 ) = " "; ## Remove '-'

			# The previous line is probably the deletion of the blank line before the block
			( $i > 0 ) and ( $hHunk->{lines}[ $i - 1 ] =~ /^-/ ) and $hHunk->{lines}[ $i - 1 ] = " ";

			$is_sleep_block = 1;
			next;
		} ## end if ( $$line =~ m,^\-\[Sleep\],)

		# Remove deletions of lines in our [Sleep] block
		$is_sleep_block
		and ( $$line =~ m,^-, )
		and substr( $$line, 0, 1 ) = " " ## Remove '-'
		and next;

		# No sleep block
		$is_sleep_block = 0;

	} ## End of looping lines

	return 1;
} ## end sub protect_config

# -----------------------------------------------------------------------
# --- Remove unused prefix and postfix lines. Recalculates offsets.   ---
# -----------------------------------------------------------------------
sub prune_hunk {

	# Early exits:
	defined( $hHunk ) or return 0;
	$hHunk->{useful} or return 0;

	# Go through the lines and see what we've got.
	my @mask_info = ( $hHunk->{masked_start} );
	my $prefix    = 0;
	my $postfix   = 0;
	my $changed   = 0; ## Set to 1 once the first change was found.

	for ( my $i  = 0; $i < $hHunk->{count}; ++$i ) {
		my $line = $hHunk->{lines}[$i]; ## Shortcut
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
				is_mask_end( $line ) ? -1
				: is_mask_else( $line ) ? -1
				  : is_mask_start( $line ) ? 1
				    : 0;
		} ## end if ( 0 == $changed )

		# Note: The last action still stands, no matter whether it gets pruned
		#       or not, as it is only relevant for the next hunk.
	} ## End of analyzing the hunks lines.

	# Now let's prune it:
	if ( $prefix > 3 ) {
		$prefix -= 3;
		splice( @{ $hHunk->{lines} }, 0, $prefix );
		$hHunk->{src_start} += $prefix;
		$hHunk->{count}     -= $prefix;

		# If any mask state change gets pruned, we have to remember the last one:
		for ( my $i = $prefix; $i >= 0; --$i ) {
			if ( $mask_info[$i] ) {
				$hHunk->{masked_start} = $mask_info[$i] > 0 ? 1 : 0;
				last;
			}
		} ## end for ( my $i = $prefix ;...)
	}     ## end if ( $prefix > 3 )
	if ( $postfix > 3 ) {
		$postfix -= 3;
		splice( @{ $hHunk->{lines} }, $hHunk->{count} - $postfix, $postfix );
		$hHunk->{count} -= $postfix;
	}

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
		close( $fIn );
	} else {
		die( "$in can not be opened for reading! [$!]" );
	}

	# Now prepare the output, line by line.
	my $is_block = 0;
	my $is_else  = 0;
	my $line_no  = 0;
	for my $line ( @lIn ) {

		chomp $line;
		++$line_no;

		if ( is_mask_start( $line ) ) {
			if ( $is_block > 0 ) {
				print "ERROR: $in:$line_no : Mask start in mask!\n";
				die( "Illegal file" );
			}
			$is_block = 1;
		} elsif ( is_mask_else( $line ) ) {
			if ( 0 == $is_block ) {
				print "ERROR: $in:$line_no : Mask else outside mask!\n";
				die( "Illegal file" );
			}
			$is_else = 1;
		} elsif ( is_mask_end( $line ) ) {
			if ( 0 == $is_block ) {
				print "ERROR: $in:$line_no : Mask end outside mask!\n";
				die( "Illegal file" );
			}
			$is_block = 0;
			$is_else  = 0;
		} elsif ( $is_block
		          && !$is_else
		          && ( "# #" ne substr( $line, 0, 3 ) )
		          && ( "  * " ne substr( $line, 0, 4 ) ) ) {
			$hFile{source} =~ m/\.sym\.pwx$/ and $line = "  * " . $line
			or $line                                   = "# " . $line;

			# Do not create empty comment lines with trailing spaces.
			$line =~ s/(#)\s+$/$1/;
		} ## end elsif ( $is_block && !$is_else...)

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open( my $fOut, ">", $out ) ) {
		for my $line ( @lOut ) {
			print $fOut "$line\n";
		}
		close( $fOut );
	} else {
		die( "$out can not be opened for writing! [$!]" );
	}

	# Remove the temporary file
	unlink( $in );

	# Now prepare the patch. It is like above, but with less checks.
	# We have to move out the lines first, and then write them back.
	$is_block = 0;
	$is_else  = 0;
	@lIn      = splice( @{ $hFile{output} } );

	for my $line ( @lIn ) {
		if ( $line =~ m/#\s+masked_(?:start|end)\s+([01])$/ ) {
			$1 and $is_block       = 1 or $is_block = 0;
			$is_block and $is_else = 0; ## can't be.
			next;                       ## do not transport this line
		}
		is_mask_end( $line ) and $is_block   = 0;
		is_mask_start( $line ) and $is_block = 1;
		$is_block or $is_else                = 0;
		is_mask_else( $line ) and $is_else   = 1;
		$is_block
		and ( !$is_else )
		and '@@' ne substr( $line, 0, 2 )
		and ( !( $line =~ m/^[- ]+#(?:if|else|endif)/ ) )
		and substr( $line, 1, 0 ) = "# ";

		# Make sure not to demand to add empty comment lines with trailing spaces
		$line =~ s/^(\+#)\s+$/$1/;
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
		close( $fIn );
	} else {
		die( "$in can not be opened for reading! [$!]" );
	}

	# Now prepare the output, line by line.
	my $is_block = 0;
	my $is_else  = 0;
	my $line_no  = 0;
	for my $line ( @lIn ) {

		chomp $line;
		++$line_no;

		if ( is_mask_start( $line ) ) {
			if ( $is_block > 0 ) {
				print "ERROR: $in:$line_no : Mask start in mask!\n";
				die( "Illegal file" );
			}
			$is_block = 1;
		} elsif ( is_mask_else( $line ) ) {
			if ( 0 == $is_block ) {
				print "ERROR: $in:$line_no : Mask else outside mask!\n";
				die( "Illegal file" );
			}
			$is_else = 1;
		} elsif ( is_mask_end( $line ) ) {
			if ( 0 == $is_block ) {
				print "ERROR: $in:$line_no : Mask end outside mask!\n";
				die( "Illegal file" );
			}
			$is_block = 0;
			$is_else  = 0;
		} elsif ( $is_block && !$is_else ) {
			$line =~ s/--/&#x2D;&#x2D;/g;
		}

		push @lOut, $line;
	} ## end for my $line (@lIn)

	# Now write the outfile:
	if ( open( my $fOut, ">", $out ) ) {
		for my $line ( @lOut ) {
			print $fOut "$line\n";
		}
		close( $fOut );
	} else {
		die( "$out can not be opened for writing! [$!]" );
	}

	# Remove the temporary file
	unlink( $in );

	# Now prepare the patch. It is like above, but with less checks.
	# We have to move out the lines first, and then write them back.
	@lIn      = ();
	$is_block = 0;
	$is_else  = 0;
	@lIn      = splice( @{ $hFile{output} } );
	for my $line ( @lIn ) {
		if ( $line =~ m/#\s+masked_(?:start|end)\s+([01])$/ ) {
			$1 and $is_block       = 1 or $is_block = 0;
			$is_block and $is_else = 0; ## can't be.
			next;                       ## do not transport this line
		}
		is_mask_end( $line ) and $is_block   = 0;
		is_mask_start( $line ) and $is_block = 1;
		$is_block or $is_else                = 0;
		is_mask_else( $line ) and $is_else   = 1;
		$is_block
		and ( !$is_else )
		and $line =~ s/([^<!]+)--([^>]+)/${1}&#x2D;&#x2D;${2}/g;

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

	# Early exits:
	defined( $hHunk ) or return 1;
	$hHunk->{useful} or return 1;

	# We must know when "needed by elogind blocks" start
	my $in_elogind_block = 0;
	for ( my $i          = 0; $i < $hHunk->{count}; ++$i ) {
		my $line         = \$hHunk->{lines}[$i]; ## Shortcut

		# Note down removals of includes we commented out
		if ( $$line =~ m,^-\s*/[/*]+\s*#include\s+([<"'])([^>"']+)[>"']\s*(?:\*/)?, ) {
			$hIncs{$2}{remove} = {
				hunkid => $hHunk->{idx},
				lineid => $i,
				sysinc => $1 eq "<"
			};
			next;
		} ## end if ( $$line =~ m,^-\s*/[/*]+\s*#include\s+([<"'])([^>"']+)[>"']\s*(?:\*/)?,)

		# Note down inserts of possibly new includes we might want commented out
		if ( $$line =~ m,^\+\s*#include\s+([<"'])([^>"']+)[>"'], ) {
			$hIncs{$2}{insert} = {
				elogind  => $in_elogind_block,
				hunkid   => $hHunk->{idx},
				lineid   => $i,
				spliceme => 0,
				sysinc   => $1 eq "<"
			};
			next;
		} ## end if ( $$line =~ m,^\+\s*#include\s+([<"'])([^>"']+)[>"'],)

		# Note down removals of includes we explicitly added for elogind
		if ( $in_elogind_block
		     && ( $$line =~ m,^-\s*#include\s+([<"'])([^>"']+)[>"'], ) ) {
			$hIncs{$2}{elogind} = { hunkid => $hHunk->{idx}, lineid => $i };
			next;
		} ## end if ( $in_elogind_block...)

		# elogind include blocks are started by a comment featuring "needed by elogind"
		if ( $$line =~ m,^[ -]\s*/+.*needed\s+(?:by|for)\s+elogind.*,i ) {
			$in_elogind_block = 1;
			next;
		}

		# elogind include blocks end, when the first not removed *EMPTY* line is found
		$in_elogind_block and ( $$line =~ m,^[ ]\s*$, ) and $in_elogind_block = 0;
	} ## end for ( my $i = 0 ; $i < ...)

	return 1;
} ## end sub read_includes

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
			$hId > -1 or print "splice_includes : Inc $inc has Hunk Id -1!\n" and next;
			if ( -1 == $lId ) {
				$hHunk = $hFile{hunks}[$hId];
				hunk_failed( "splice_includes: $inc has line id -1!" );
				next;
			}
			if ( $lId >= $hFile{hunks}[$hId]{count} ) {
				$hHunk = $hFile{hunks}[$hId];
				hunk_failed( "splice_includes: $inc line id $lId/$hFile{hunks}[$hId]{count}!" );
				next;
			}

			# Record the include line
			$incMap{$hId}{$lId} = 1;
		} ## end if ( $hIncs{$inc}{insert...})
	}     ## end for my $inc ( keys %hIncs)

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

# Callback function for File::Find
sub wanted {
	my $f         = $File::Find::name;
	my $is_wanted = 0;

	$f =~ m,^\./, or $f = "./$f";

	-f $_
	and ( ( 0 == $have_wanted ) or defined( $hWanted{$f} ) )
	and ( !( $_ =~ m/\.pwx$/ ) )
	and ( !( $File::Find::name =~ m,man/rules/, ) ) ## Protect generated man rules (Issue #3)
	and push @source_files, $File::Find::name
	and $is_wanted = 1;

	$is_wanted and $hWanted{$f} = 2;

	return 1;
} ## end sub wanted
