#!/usr/bin/perl -w

# ================================================================
# ===        ==> --------     HISTORY      -------- <==        ===
# ================================================================
#
# Version  Date        Maintainer      Changes, Additions, Fixes
# 0.0.1    2018-05-02  sed, PrydeWorX  First basic design.
# 0.0.2    2018-05-07  sed, PrydeWorX  Work flow integrated up to creating the formatted patches.
# 0.0.3    2018-05-13  sed, PrydeWorX  Reworking of the formatted patches added.
# 0.1.0    2018-05-14  sed, PrydeWorX  Application of the reworked patches added.
# 0.2.0    2018-05-15  sed, PrydeWorX  First working version.
# 0.2.1                                Fixed usage of Try::Tiny.
# 0.2.2    2018-05-16  sed, PrydeWorX  Made sure that the commit file is always written on exit,
#                                        but only if a potential commits file was finished reading.
# 0.3.0    2018-06-22  sed, PrydeWorX  Be sure to only send --create to check_tree.pl if the file
#                                        is not already existing.
# 0.4.0    2019-01-27  sed, PrydeWorX  Switch from topological to chronological order.
# 0.4.1    2019-02-20  sed, PrydeWorX  Do not consider files in man/rules/ (Issue #3)
# 0.4.2    2022-12-21  sed, PrydeWorX  Try to remedy patch failures by looking for missing commits in between.
# 0.4.3    2023-10-25  sed, EdenWorX   If merge commits were skipped, substract them from the total commit count.
# 0.4.4    2023-12-29  sed, EdenWorX   If a merge does not work, try to patch directly. If this also fails, give
#                                        detailed instructions to the user about how to continue.
# 0.4.5    2025-05-23  sed, EdenWorX   Do not try to apply mutual commits again.
# 0.5.0    2025-06-11  sed, EdenWorX   Modernized, use Getopt instead of old c-style loops, split up spaghetti code.
#
# ========================
# === Little TODO list ===
# ========================
#
use strict;
use warnings;
use Carp;
use Cwd qw( getcwd abs_path );
use File::Basename;
use File::Find;
use Getopt::Long;
use Git::Wrapper;
use Readonly;
use Try::Tiny;

# ================================================================
# ===        ==> ------ Constants and Helpers ----- <==        ===
# ================================================================
Readonly my $DASH  => q{-};
Readonly my $DOT   => q{.};
Readonly my $EMPTY => q{};
Readonly my $PIPE  => q{|};
Readonly my $SLASH => q{/};
Readonly my $SPACE => q{ };

my $PROGDIR;
my $PROGNAME;

BEGIN {
	use File::Basename;
	my $program_path = -l __FILE__ ? readlink __FILE__ : __FILE__;
	$PROGDIR  = dirname($program_path)  // $DOT;
	$PROGNAME = basename($program_path) // $EMPTY;

} ## end BEGIN

Readonly my $VERSION     => '0.4.5';                                                      ## Please keep this current!
Readonly my $VERSMIN     => $DASH x length($VERSION);
Readonly my $WORKDIR     => getcwd();
Readonly my $CHECK_TREE  => abs_path( $PROGDIR . '/check_tree.pl' );
Readonly my $COMMIT_FILE => abs_path( $PROGDIR . '/last_mutual_commits.csv' );
Readonly my $USAGE_SHORT => "$PROGNAME <--help|[OPTIONS] <-u upstream path> <-r refid>>";
Readonly my $USAGE_LONG => $EMPTY
  . "elogind git tree migration V$VERSION\n"
  . "----------------------------$VERSMIN\n" . "\n"
  . "  Reset the git tree in <upstream path> to the <refid>. The latter can be any\n"
  . "  commit, branch or tag. Then search its history since the last mutual commit\n"
  . "  for any commit that touches at least one file in any subdirectory of the\n"
  . "  directory this script was called from.\n" . "\n"
  . "  Please note that this program was written especially for elogind. It is very\n"
  . "  unlikely that it can be used in any other project.\n" . "\n"
  . "USAGE:\n"
  . "  $USAGE_SHORT\n" . "\n"
  . "OPTIONS:\n"
  . "  -u|--upstream <path>: Path to the upstream to migrate.\n"
  . "  -r|--refid <refid>  : reference id to check out first in upstream.\n"
  . "     --advance        : Use the last upstream commit that has been written\n"
  . "                        into \"$COMMIT_FILE\" as the last\n"
  . "                        mutual commit to use. This is useful for continued\n"
  . "                        migration of branches. Incompatible with -c|--commit.\n"
  . "  -c|--commit <hash>  : The mutual commit to use. If this option is not used,\n"
  . "                        the script looks into \"$COMMIT_FILE\"\n"
  . "                        and uses the commit noted for <refid>. Incompatible\n"
  . "                        with --advance.\n"
  . "                        Note: The mutual commit is not applied again.\n"
  . "  -h|--help           : Show this help and exit.\n"
  . "  -o|--output <path>  : Path to where to write the patches. The default is to\n"
  . "                        write into \"$PROGDIR/patches\".\n" . "\n"
  . "Notes:\n"
  . "  - The upstream tree is reset and put back into the current state after the\n"
  . "    script finishes.\n"
  . "  - When the script succeeds, it adds a line to \"$COMMIT_FILE\"\n"
  . "    of the form:\n"
  . "    <tag>-last <newest found commit>. You can use that line for the next\n"
  . "    <refid> you wish to migrate to.\n";

# ================================================================
# ===        ==> -------- Global variables -------- <==        ===
# ================================================================

my $commit_count   = 0;       # It is easiest to count the relevant commits globally.
my $commits_read   = 0;       # Set to one once the commit file is completely read.
my $do_advance     = 0;       # If set by --advance, use src-<hash> as last commit.
my %hDirectories   = ();      # Filled when searching relevant files, used to validate new files.
my %hPatches       = ();      # A simple reverse hash to get from file to index in @lPatches
my %hRefIDs        = ();      # A simple hash to get from ref id to index in @lPatches
my %hSrcCommits    = ();      # Record here which patch file is which commit.
my @lCommits       = ();      # List of all relevant commits that have been found, in topological order.
my $main_result    = 1;       # Used for parse_args() only, as simple $result is local everywhere.
my $mutual_commit  = $EMPTY;  # The last mutual commit to use. Will be read from csv if not set by args.
my $output_path    = $EMPTY;
my @lPatches       = ();      # List of hashrefs with the patch information (File, refid, whether applied or not)
my $previous_refid = $EMPTY;  # Store current upstream state, so we can revert afterwards.
my $prg_line       = $EMPTY;  # Current line when showing progress
my $show_help      = 0;
my @source_files   = ();      # Final file list to process, generated in in generate_file_list().
my $upstream_path  = $EMPTY;
my $wanted_refid   = $EMPTY;  # The refid to reset the upstream tree to.

# ================================================================
# ===        ==> ------- MAIN DATA STRUCTURES ------ <==       ===
# ================================================================
my %hCommits = ();  # Hash of all upstream commits that touch at least one file:

# ( refid : count of files touched )
my %hFiles = ();    # List of all source files as %hFile structures with a simple

# ( tgt : $hFile ) mapping.
my $hFile = {};     # Simple description of one file consisting of:

# Note: The store is %hFiles, this is used as a global pointer.
#       Further although the target is the key in %hFiles, we
#       store it here, too, so we always no the $hFile's key.
# ( patch: Full path to the patch that check_tree.pl would generate
#   src  : The potential relative upstream path with 'elogind' substituted by 'systemd'
#   tgt  : The found relative path in the local tree
# )
my %hMutuals = ();  # Mapping of the $COMMIT_FILE, that works as follows:

# CSV lines are structured as:
# <refid> <hash> src-<hash> tgt-<hash>
# They map as follows:
# ( <path to upstream tree> {
#       <refid> : {
#           mutual : <hash> | This is the last mutual commit
#           src    : <hash> | This is the last individual commit in the upstream tree (*)
#           tgt    : <hash> | This is the last individual commit in the local tree    (*)
#       } } )
# (*) When this entry was written. This means that src-<hash> can be used as
#     the next last mutual commit, when this migration run is finished. To make
#     this automatic, the --advance option triggers exactly that.
my %hPatchTgts = ();  # Maps {patch_file} to {tgt1 => 1, tgt2 => 1, ..., tgtn => 1}

# set signal-handlers
local $SIG{'INT'}  = \&handle_sig;
local $SIG{'QUIT'} = \&handle_sig;
local $SIG{'TERM'} = \&handle_sig;

# ================================================================
# ===        ==> --------    Prechecks     -------- <==        ==
# ================================================================

-x $CHECK_TREE or croak("$CHECK_TREE not found!");

$output_path = abs_path("$PROGDIR/patches");
my %program_options = (
	'advance+'     => \$do_advance,
	'commit|c=s'   => \$mutual_commit,
	'help|h+'      => \$show_help,
	'output|o=s'   => \$output_path,
	'upstream|u=s' => \$upstream_path,
	'refid|r=s'    => \$wanted_refid
);
GetOptions(%program_options) or $show_help = -2;
$output_path = abs_path($output_path);
if ( !$show_help && !length($wanted_refid) ) {
	print "ERROR: Please provide a path to upstream and a refid!\n\nUsage: $USAGE_SHORT\n";
	$main_result = 0;
}

# If both --advance and --commit were used, we can not tell what the
# user really wants. So better be safe here, or we might screw the tree!
if ( $do_advance && length($mutual_commit) ) {
	print "ERROR: You have used both --advance and --commit.\n";
	print "       Which one is the one you really want?\n\n";
	print "Usage: $USAGE_SHORT\n";
	$main_result = 0;
} ## end if ( $do_advance && length...)

# Show help if wanted or provoked
( 0 != $show_help ) and print "$USAGE_LONG" and exit( !$main_result );
( 0 == $main_result ) and exists(42);

# Further preparations
get_last_mutual() and generate_file_list()        or exit 1;
checkout_tree( $upstream_path, $wanted_refid, 1 ) or exit 1;

# ================================================================
# ===        ==> -------- = MAIN PROGRAM = -------- <==        ===
# ================================================================

# -----------------------------------------------------------------
# --- 1) Go through all files and generate a list of all source ---
# ---    commits that touch the file.                           ---
# -----------------------------------------------------------------
print 'Searching relevant commits ...';
for my $file_part (@source_files) {
	build_hFile($file_part) or next;
	build_hCommits()        or next;
}
show_prg($EMPTY);
printf( " %d commits found\n", $commit_count );

# -----------------------------------------------------------------
# --- 2) Get a list of all commits and build @lCommits, checking --
# ---    against the found hashes in $hCommits. This will build ---
# ---    a list that has the correct order the commits must be  ---
# ---    applied.                                               ---
# -----------------------------------------------------------------
build_lCommits() or exit 1;

# -----------------------------------------------------------------
# --- 3) Go through the relevant commits and create formatted   ---
# ---    patches for them.                                      ---
# -----------------------------------------------------------------
build_lPatches() or exit 1;

# -----------------------------------------------------------------
# --- 4) Go through the patches and rewrite them. We only want  ---
# ---    them to touch files of relevance, and need them to     ---
# ---    contain only diffs that are valid for us. We'll use    ---
# ---    check_tree.pl to achieve the latter.                   ---
# -----------------------------------------------------------------
for my $i ( 0 .. ( $commit_count - 1 ) ) {
	my $fmt    = sprintf( '%04d-*.patch', $i + 1 );
	my @lFiles = glob qq("${output_path}/${fmt}");

	# Be sure this is solid!
	# ----------------------------------------------------------
	if ( scalar @lFiles > 1 ) {
		print "\nERROR: $fmt results in more than one patch!\n";
		exit 1;
	} elsif ( 1 > scalar @lFiles ) {
		print "\nERROR: No patches found for $fmt!\n";
		exit 1;
	}

	my $file = basename( $lFiles[0] );
	my $id   = $hPatches{$file};
	defined($id)                         or print "\nERROR: $lFiles[0] not listed in hPatches!\n" and return 0;
	defined( $lPatches[$id]{'applied'} ) or print "\nERROR: $lFiles[0] not listed in lPatches!\n" and return 0;

	# If the patch was already applied (for some error recoverage) then skip it.
	( 1 == $lPatches[$id]{'applied'} ) and show_prg("Skipping $file - already applied") and next;

	# Now rework the patch
	# ---------------------------------------------------------
	show_prg( sprintf( 'Reworking %s', basename( $lFiles[0] ) ) );
	my $r = rework_patch( $lFiles[0] );
	$r or exit 1;     ## Error detected
	$r < 0 and next;  ## Empty patch

	# -------------------------------------------------------------
	# --- 5) Reworked patches must be applied directly.         ---
	# ---    Otherwise we'll screw up if a newly created file   ---
	# ---    gets patched later.                                ---
	# -------------------------------------------------------------
	show_prg( sprintf( 'Applying  %s', basename( $lFiles[0] ) ) );
	$r = apply_patch( $lFiles[0] );

	if ( 0 == $r ) {
		exit 1;
	}

	# The patch file is no longer needed. Keeping it would lead to confusion.
	unlink( $lFiles[0] );
} ## end for my $i ( 0 .. ( $commit_count...))
show_prg($EMPTY);

# ===========================
# === END OF MAIN PROGRAM ===
# ===========================

# ================================================================
# ===        ==> --------     Cleanup      -------- <==        ===
# ================================================================

END {
	set_last_mutual();
	length($previous_refid) and checkout_tree( $upstream_path, $previous_refid, 0 );
}

# ================================================================
# ===        ==> ---- Function Implementations ---- <==        ===
# ================================================================

sub add_source_file {
	my ($f) = @_;

	( -e $f ) and ( -f $f ) and push @source_files, $f;

	return 1;
} ## end sub add_source_file

# --------------------------------------------------------------
# --- Apply a reworked patch                                 ---
# --------------------------------------------------------------
sub apply_patch {
	my ($pFile)     = @_;
	my $git         = Git::Wrapper->new($WORKDIR);
	my @lGitRes     = ();
	my $patch_lines = $EMPTY;

	# --- Ensure everything is solid ---
	# ----------------------------------
	my $file = basename($pFile);
	my $id   = $hPatches{$file};
	defined($id)                         or print "\nERROR: $file not listed in hPatches!\n" and return 0;
	defined( $lPatches[$id]{'applied'} ) or print "\nERROR: $file not listed in lPatches!\n" and return 0;

	# If the patch was already applied, do not try it again.
	( 1 == $lPatches[$id]{'applied'} ) and return 1;

	# --- 1) Read the patch, we have to use it directly via STDIN ---
	# ---------------------------------------------------------------
	if ( open( my $fIn, '<', $pFile ) ) {
		my @lLines = <$fIn>;
		close($fIn) or croak("Closing $pFile FAILED: $!\n");
		chomp(@lLines);
		$patch_lines = join( "\n", @lLines ) . "\n";
	} else {
		print "\nERROR [apply]: $pFile could not be opened for reading!\n$!\n";
		return 0;
	}

	# --- 2) Try to apply the patch as is                         ---
	# ---------------------------------------------------------------
	my $result = 0;

	try {
		@lGitRes = $git->am(
			{
				'3'    => 1,
				-STDIN => $patch_lines
			}
		);
		$result = 1;
	} catch {
		show_prg( sprintf( "Applying %s with 'git am' failed!", $file ) );
	};

	if ( 0 == $result ) {

		# --- 3) Try to apply the patch directly                      ---
		# ---------------------------------------------------------------
		show_prg( sprintf( "Applying %s directly\n", $file ) );
		my @patch = ( '/usr/bin/patch', '-p', '1', '-i', $pFile );
		if ( system(@patch) ) {

			# We have to fix this by hand... great...
			printf( "\nApplying %s directly FAILED [%d]\n", $file, ( $? & 127 ) );
			print("Fix above errors, add all files to git, issue 'git am --continue' and\n");
			printf( "Set last mutual commit to '%s'\n", shorten_refid( $upstream_path, $hSrcCommits{$pFile} ) );
			exit 1;
		} else {

			# We have to add all relevant target files before "am" can continue
			for my $tgt ( keys %{ $hPatchTgts{$pFile} } ) {
				$git->add($tgt);
			}
			try {
				$git->am( { 'continue' => 1 } );
				$result = 1;
			} catch {

				# Let's try with a direct patch, git apply can not apply fuzzy
				$git->am( { 'abort' => 1 } );
				show_prg( sprintf( "Applying  %s FAILED\n", $file ) );
			};
		} ## end else [ if ( system(@patch) ) ]
	} ## end if ( 0 == $result )

	# --- 4) If this did not work, try to apply missing patches, then this one. ---
	# -----------------------------------------------------------------------------
	if ( 0 == $result ) {
		print "Trying to identify missing commits ...\n";

		my $prv_rid = $previous_refid;

		( $prv_rid ne $wanted_refid ) and checkout_tree( $upstream_path, $wanted_refid, 1 );

		my $refid  = $lPatches[$id]{'refid'};
		my $mutual = $hMutuals{$upstream_path}{$wanted_refid}{mutual_full};
		my @lRev   = ();
		my $done   = 0;                                                     ## Don't return 1 if this stays being zero or we'll get an endless loop if nothing appliable is found!

		if ( defined($mutual) ) {
			try {
				my $git_ex = Git::Wrapper->new($upstream_path);
				@lRev = $git_ex->rev_list( { 'reverse' => 1, 'no-merges' => 1, 'full-history' => 1, 'dense' => 1, 'topo-order' => 1 }, "${mutual}...${refid}" );
			} catch {
				print "ERROR: Couldn't fetch commits\n";
				print 'Exit Code : ' . $_->status . "\n";
				print 'Message   : ' . $_->error . "\n";
				return 0;
			};

			print 'It looks like we were missing ' . ( scalar @lRev ) . " commits. Trying to apply the relevant ones...\n";

			for my $line (@lRev) {
				chomp $line;

				if ( defined( $hCommits{$line} ) && ( $mutual ne $hCommits{$line} ) ) {

					# The commit is relevant for us
					my $next_id = $hRefIDs{$line};
					defined($next_id) and ( 0 == $lPatches[$next_id]{'applied'} ) or next;

					foreach my $next_patch ( @{ $lPatches[$next_id]{'paths'} } ) {
						( -f "$output_path/$next_patch" ) and ( $file ne $next_patch ) and $done += apply_patch("$output_path/$next_patch");
					}
				} ## end if ( defined( $hCommits...))
			} ## end for my $line (@lRev)
		} else {
			print "No known last mutual commit, breaking off!\n";
		}

		# Revert to where we were
		( $prv_rid ne $previous_refid ) and checkout_tree( $upstream_path, $prv_rid, 1 );

		# Now, if $done is greater than 1, we can try the failed commit again
		print "Applied $done commits.\n";
		( $done > 0 ) and $result = apply_patch($pFile);
	} ## end if ( 0 == $result )

	( $result > 0 ) or return $result;  ## Give up and exit if everything fails

	# --- 5) Get the new commit id, so we can update %hMutuals ---
	# ---------------------------------------------------------------
	$hMutuals{$upstream_path}{$wanted_refid}{tgt} = shorten_refid( $WORKDIR, 'HEAD' );
	length( $hMutuals{$upstream_path}{$wanted_refid}{tgt} ) or return 0;  # Give up and exit

	# The commit of the just applied patch file becomes the last mutual commit.
	$hMutuals{$upstream_path}{$wanted_refid}{mutual_full} = $hSrcCommits{$pFile};
	$hMutuals{$upstream_path}{$wanted_refid}{mutual} =
	  shorten_refid( $upstream_path, $hSrcCommits{$pFile} );
	length( $hMutuals{$upstream_path}{$wanted_refid}{mutual} ) or return 0;  # Give up and exit

	# --- 6) "Tick off" the patch in our patch list ---
	# ------------------------------------------------------------------
	( $result > 0 ) and $lPatches[$id]{'applied'} = 1;

	return $result;
} ## end sub apply_patch

# ------------------------------------------------------
# --- Build a hash of commits for the current hFile. ---
# ------------------------------------------------------
sub build_hCommits {
	my $git  = Git::Wrapper->new($upstream_path);
	my @lRev = $git->rev_list( {}, "${mutual_commit}...${wanted_refid}", $hFile->{src} );

	for my $line (@lRev) {
		chomp $line;
		( $line eq $mutual_commit ) and next;  ## Don't apply what has been applied already
		defined( $hCommits{$line} )
		  or ++$commit_count and $hCommits{$line} = 0;
		++$hCommits{$line};
	} ## end for my $line (@lRev)

	return 1;
} ## end sub build_hCommits

# --------------------------------------------------------------------
# --- Build a list of the relevant commits in chronological order. ---
# --------------------------------------------------------------------
sub build_lCommits {
	my $git = Git::Wrapper->new($upstream_path);

	my @lRev = $git->rev_list( { 'reverse' => 1, 'no-merges' => 1, 'full-history' => 1, 'dense' => 1, 'topo-order' => 1 }, "${mutual_commit}...${wanted_refid}" );

	for my $line (@lRev) {
		chomp $line;
		( $line eq $mutual_commit ) and next;  ## Don't apply what has been applied already
		defined( $hCommits{$line} )
		  and show_prg("Noting down $line")
		  and push @lCommits, "$line";
	} ## end for my $line (@lRev)
	show_prg($EMPTY);

	return 1;
} ## end sub build_lCommits

# ----------------------------------------------------------
# --- Add an entry to hFiles for a specific target file. ---
# ----------------------------------------------------------
sub build_hFile {
	my ($tgt) = @_;

	defined($tgt) and length($tgt) or print("ERROR\n") and croak('build_hfile: tgt is empty ???');

	# We only prefixed './' to unify things. Now it is no longer needed:
	$tgt =~ s,^[.]/,,ms;

	# Check the target file
	my $src = "$tgt";
	$src =~ s/elogind/systemd/msg;
	$src =~ s/[.]pwx$//ms;
	-f "$upstream_path/$src" or return 0;

	# Build the patch name
	my $patch = $tgt;
	$patch =~ s/\//_/msg;

	# Build the central data structure.
	$hFiles{$tgt} = {
		patch => $output_path . $SLASH . $patch . '.patch',
		src   => $src,
		tgt   => $tgt
	};

	# This is now our current hFile
	$hFile = $hFiles{$tgt};

	return 1;
} ## end sub build_hFile

# ----------------------------------------------------------------
# --- Fill $output_path with formatted patches from @lCommits. ---
# ----------------------------------------------------------------
sub build_lPatches {
	my $git    = Git::Wrapper->new($upstream_path);
	my $cnt    = 0;
	my @lRev   = ();
	my @lPath  = ();
	my $result = 1;

	for my $refid (@lCommits) {
		@lRev = $git->rev_list( { '1' => 1, oneline => 1 }, $refid );

		show_prg( sprintf( 'Building %03d: %s', ++$cnt, substr( $lRev[0], 0, 49 ) ) );

		try {
			@lPath = $git->format_patch(
				{
					'1'                  => 1,
					'find-copies'        => 1,
					'find-copies-harder' => 1,
					'numbered'           => 1,
					'output-directory'   => $output_path
				},
				"--start-number=$cnt",
				$refid
			);
		} catch {
			print "\nERROR: Couldn't format-patch $refid\n";
			print 'Exit Code : ' . $_->status . "\n";
			print 'Message   : ' . $_->error . "\n";
			$result = 0;
		};

		$result or return $result;

		# Write down the paths relevant for this:
		while ( my $path = shift @lPath ) {
			my $file = basename($path);
			defined( $hPatches{$file} ) and print "\nERROR: $file already exists in hPatches!\n" and exit 1;
			$hPatches{$file} = $cnt;
			if ( defined( $lPatches[$cnt]{paths} ) ) {
				push( @{ $lPatches[$cnt]{paths} }, $file );
			} else {
				$lPatches[$cnt] = {
					'applied' => 0,
					'paths'   => [$file],
					'refid'   => $refid
				};
			} ## end else [ if ( defined( $lPatches...))]
			defined( $hRefIDs{$refid} ) or $hRefIDs{$refid} = $cnt;
		} ## end while ( my $path = shift ...)
	} ## end for my $refid (@lCommits)

	# Show what we've got and fix the commit count if merge commits were skipped
	if ( $cnt > 0 ) {
		my $merge_commits = $commit_count - $cnt;
		show_prg($EMPTY);

		( $merge_commits >= 0 ) or print "ERROR: More commits found than listed? ($cnt > $commit_count)\n" and exit 1;

		print("$cnt / $commit_count patches built, $merge_commits merge commits skipped.\n");
		$commit_count -= $merge_commits;
	} ## end if ( $cnt > 0 )

	return 1;
} ## end sub build_lPatches

# -------------------------------------------------------
# --- Use check_tree.pl on the given commit and file. ---
# -------------------------------------------------------
sub check_tree {
	my ( $commit, $file, $isNew ) = @_;
	my $stNew = $EMPTY;

	# If this is the creation of a new file, the hFile must be built.
	if ( $isNew > 0 ) {
		my $tgt_file = basename($file);
		my $tgt_dir  = dirname($file);
		$tgt_file =~ s/systemd/elogind/msg;

		defined( $hDirectories{$tgt_dir} )
		  or $tgt_dir =~ s/systemd/elogind/msg;

		my $tgt = "$tgt_dir/$tgt_file";

		# Build the patch name
		my $patch = $tgt;
		$patch =~ s/\//_/msg;
		$hFiles{$file} = {
			patch => $output_path . $SLASH . $patch . '.patch',
			src   => $file,
			tgt   => $tgt
		};
		$stNew = '--create ';
	} ## end if ( $isNew > 0 )
	my $path = $hFiles{$file}{patch};

	# Now get the patch built
	my @lResult = `$CHECK_TREE --stay -c $commit ${stNew}-f $file $upstream_path 2>&1`;
	my $res     = $?;
	my $err     = $!;

	if ( $res != 0 ) {
		print "\n$CHECK_TREE died!\n";

		if ( $res == -1 ) {
			print "failed to execute: $err\n";
		} elsif ( $? & 127 ) {
			printf "Signal %d, %s coredump\n", ( $? & 127 ), ( $? & 128 ) ? 'with' : 'without';
		} else {
			printf "child exited with value %d\n", $? >> 8;
		}
		print "-----\n" . join( $EMPTY, @lResult ) . "-----\n";
		return $EMPTY;
	} ## end if ( $res != 0 )

	# If check_tree found no diff or cleaned up all hunks, no patch is created.
	for my $line (@lResult) {
		chomp $line;
		if ( $line =~ m/${file}:\s+(clean|same)/msx ) {
			return 'none';
		}
	} ## end for my $line (@lResult)

	return $path;
} ## end sub check_tree

# -----------------------------------------------------------------------
# --- Checkout the given refid on $upstream_path                      ---
# --- Param 1 is the path where to do the checkout
# --- Param 2 is the refid to check out.                              ---
# --- Param 3 can be set to 1, if mutuals{src} and previous_refid     ---
# ---         shall be stored.                                        ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub checkout_tree {
	my ( $path, $commit, $do_store ) = @_;

	# It is completely in order to not wanting to checkout a specific commit.
	defined($commit) and length($commit) or return 1;

	my $git        = Git::Wrapper->new($path);
	my $new_commit = $EMPTY;
	my $old_commit = shorten_refid( $path, 'HEAD' );

	# The current commit must be valid:
	length($old_commit) or return 0;

	# Get the shortened commit hash of $commit
	$new_commit = shorten_refid( $path, $commit );
	length($new_commit) or return 0;

	# Now check it out, unless we are already there:
	if ( $old_commit ne $new_commit ) {
		my $result = 1;
		print "Checking out $new_commit in ${path}...";
		try {
			$git->checkout($new_commit);
		} catch {
			print "\nERROR: Couldn't checkout \"$new_commit\" in $path\n";
			print 'Exit Code : ' . $_->status . "\n";
			print 'Message   : ' . $_->error . "\n";
			$result = 0;
		};
		$result or return $result;
		print " done\n";
	} ## end if ( $old_commit ne $new_commit)

	# Save the commit hash of the wanted refid and the previous commit if wanted
	if ( $do_store > 0 ) {
		$hMutuals{$path}{$wanted_refid}{src} = $new_commit;
		$previous_refid = $old_commit;
	}

	return 1;
} ## end sub checkout_tree

# -----------------------------------------------------------------------
# --- Finds all relevant files and store them in @wanted_files        ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub generate_file_list {

	# Do some cleanup first. Just to be sure.
	print 'Cleaning up...';
	system( 'rm', ( '-rf', 'build*' ) );
	my $res = `find -iname '*.orig' -or -iname '*.bak' -or -iname '*.rej' -or -iname '*~' -or -iname '*.gc??' | xargs rm -f`;
	print " done [$res]\n";

	# The idea now is, that we use File::Find to search for files
	# in all legal directories this program allows.
	print 'Find relevant files...';
	for my $xDir ( 'doc', 'docs', 'factory', 'm4', 'man', 'po', 'shell-completion', 'src', 'tools' ) {
		if ( -d "$xDir" ) {
			find( { wanted => \&wanted, follow => 1 }, $xDir . $SLASH );
		}
	}

	# There are also root files we need to check. Thanks to the usage of
	# check_tree.pl to generate the later commit diffs, these can be safely
	# added to our file list as well.
	for my $xFile ( '.gitignore', '.mailmap', 'configure', 'configure.ac', 'Makefile', 'Makefile.am', 'meson.build', 'meson_options.txt', 'NEWS', 'TODO' ) {
		-f "$xFile" and push @source_files, "./$xFile";
	}
	print ' done - ' . ( scalar @source_files ) . " files found\n";

	# Just to be sure...
	scalar @source_files
	  or print("ERROR: No source files found? Where the hell are we?\n")
	  and return 0;

	# Eventually we can add each directory to %hDirectories
	for my $xFile (@source_files) {
		my $xDir = dirname($xFile);
		$xDir =~ s,^[.]/,,ms;
		if ( length($xDir) > 1 ) {
			defined( $hDirectories{$xDir} ) or $hDirectories{$xDir} = 1;
		}
	} ## end for my $xFile (@source_files)

	return 1;
} ## end sub generate_file_list

# ------------------------------------------------------------------------------
# --- Find or read the last mutual refid between this and the upstream tree. ---
# ------------------------------------------------------------------------------
sub get_last_mutual {

	# No matter whether the commit is set or not, we need to read the
	# commit file now, and write it back later if we have changes.
	if ( -f $COMMIT_FILE ) {
		if ( open my $fIn, '<', $COMMIT_FILE ) {
			my @lLines = <$fIn>;
			close $fIn or croak("Closing $COMMIT_FILE FAILED: $!\n");
			chomp(@lLines);

			for my $line (@lLines) {

				# Skip comments
				$line =~ m/^\s*#/ms and next;

				# Skip empty lines
				$line =~ m/^\s*$/ms and next;

				if ( $line =~ m/^\s*(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*$/msx ) {
					my $usp = $1;
					my $ref = $2;
					my $mut = $3;
					my $src = $4;
					my $tgt = $5;

					# We mast be in the right branch or right tag!
					checkout_tree( $usp, $ref, 0 ) or return 0;

					$hMutuals{$usp}{$ref} = {
						mutual => shorten_refid( $usp, $mut ),
						src    => undef,
						tgt    => undef
					};
					$src =~ m/^src-(\S+)$/ms and $hMutuals{$usp}{$ref}{src} = shorten_refid( $usp,     $1 );
					$tgt =~ m/^tgt-(\S+)$/ms and $hMutuals{$usp}{$ref}{tgt} = shorten_refid( $WORKDIR, $1 );
				} ## end if ( $line =~ m/^\s*(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*$/msx)
			} ## end for my $line (@lLines)
		} else {
			print("ERROR: $COMMIT_FILE can not be read!\n$!\n");
			return 0;
		}

		# Make sure we are back at the wanted place in the upstream tree
		checkout_tree( $upstream_path, $wanted_refid, 0 );
	} ## end if ( -f $COMMIT_FILE )

	# Note down that reading of any file is done.
	$commits_read = 1;

	# If this is already set, we are fine.
	if ( length($mutual_commit) ) {
		$hMutuals{$upstream_path}{$wanted_refid}{mutual} = shorten_refid( $upstream_path, $mutual_commit );
		length( $hMutuals{$upstream_path}{$wanted_refid}{mutual} ) or return 0;
	}

	# Now check against --advance and then set $mutual_commit accordingly.
	if ( defined( $hMutuals{$upstream_path}{$wanted_refid} ) ) {
		if ( $do_advance > 0 ) {
			defined( $hMutuals{$upstream_path}{$wanted_refid}{src} )
			  and $hMutuals{$upstream_path}{$wanted_refid}{mutual} = $hMutuals{$upstream_path}{$wanted_refid}{src}
			  or print "ERROR: --advance set, but no source hash found!\n" and return 0;
		}
		$mutual_commit = $hMutuals{$upstream_path}{$wanted_refid}{mutual};
		return 1;
	} ## end if ( defined( $hMutuals...))

	print "ERROR: There is no last mutual commit known for refid \"$wanted_refid\"!\n";

	return 0;
} ## end sub get_last_mutual

# ---------------------------------------------------------------------------
# --- Signal handler so we don't break without writing a new commit file. ---
# ---------------------------------------------------------------------------
sub handle_sig {
	my ($sig) = @_;
	print "\nCaught SIG${sig}!\n";
	exit 1;
}

# --------------------------------------------------------------
# --- Use check_tree.pl to generate valid diffs on all valid ---
# --- files within the patch with the given number.          ---
# --------------------------------------------------------------
sub rework_patch {
	my ($pFile) = @_;
	my @lLines = ();

	if ( open( my $fIn, '<', $pFile ) ) {
		@lLines = <$fIn>;
		close($fIn) or croak("Closing $pFile FAILED: $!\n");
		chomp(@lLines);
	} else {
		print "\nERROR [rework]: $pFile could not be opened for reading!\n$!\n";
		return 0;
	}

	# Copy the header, ended by either '---' or 'diff '
	# ----------------------------------------------------------
	my @lOut   = ();
	my $lCnt   = scalar @lLines;
	my $commit = $EMPTY;

	while ( $lCnt-- > 0 ) {

		# Can not be done in while(), or empty lines would break the loop.
		my $line = shift @lLines;

		# We break this once we have found a file summary line
		if ( $line =~ m/^\s+(\S+)\s+[|]\s+\d+/msx ) {
			unshift @lLines, $line;  ## Still needed
			++$lCnt;                 ## Yeah, put it up again!
			last;
		}

		# Before transfering the line, see if this is the commit info
		$line =~ m/^From\s+(\b[0-9a-fA-F]{40}\b)/msx and $commit = $1;

		push @lOut, $line;
	} ## end while ( $lCnt-- > 0 )

	# There is something wrong if we have no commit hash now
	if ( 0 == length($commit) ) {
		print "\nERROR: No 'From <hash>' line found!\n";
		return 0;
	}

	# There is something wrong if the next part is not a file summary line.
	# ----------------------------------------------------------------------
	if ( !defined( $lLines[0] ) || !( $lLines[0] =~ m/^\s+(\S+)\s+[|]\s+\d+/msx ) ) {
		print "\nERROR: No file summary block found!\n";
		print "The line currently looked at is:\n";
		print $PIPE . ( defined( $lLines[0] ) ? $lLines[0] : 'UNDEF' ) . "|\n";
		print "We still have $lCnt lines to go.\n";
		print "\nlOut so far:\n" . join( "\n", @lOut ) . "\n---------- END\n";
		return 0;
	} ## end if ( !defined( $lLines...))

	my %hFixedPatches = ();
	while ( $lCnt-- > 0 ) {
		my $isNew = 0;             ## 1 if we hit a creation summary line
		my $line  = shift @lLines;
		my $real  = $EMPTY;        ## The real file to work with
		my $src   = $EMPTY;        ## Source in upstream
		my $tgt   = $EMPTY;        ## Target in downstream

		# This ends on the first empty line.
		$line =~ m/^\s*$/ms and push( @lOut, $EMPTY ) and last;

		# This is either a line modification information, or a
		# creation line of a new file. These look like this...
		#   src/shared/meson.build                      |   1 +
		$line =~ m/^\s+(\S+)\s+[|].*/ms and $src = $1;

		# ...or that:
		#   create mode 100644 src/network/netdev/wireguard.c
		if ( $line =~ m/^\s+create\s+mode\s+\d+\s+(\S+)\s*$/msx ) {
			$src   = $1;
			$isNew = 1;
		}

		# Otherwise it is the modification summary line
		length($src) or push( @lOut, $line ) and next;

		$tgt = $src;
		$tgt =~ s/systemd/elogind/msg;

		# Let's see whether the source/target exists. Can't be a new
		# file then. This might happen if we added a missing file
		# manually beforehand.

		if ( defined( $hFiles{$tgt} ) ) {
			$real  = $tgt;
			$isNew = 0;
		} elsif ( defined( $hFiles{$src} ) ) {
			$real  = $src;
			$isNew = 0;
		} elsif ( $isNew > 0 ) {
			defined( $hDirectories{ dirname($tgt) } ) and $real = $tgt
			  or defined( $hDirectories{ dirname($src) } )
			  and $real = $src;
		}

		# We neither need diffs on invalid files, nor new files in invalid directories.
		length($real) or next;

		# Remember that the found real target is relevant for this patch
		$hPatchTgts{$pFile}{$real} = 1;

		# Now use $real to get the patch needed, if it is set.
		my $pNew = check_tree( $commit, $real, $isNew );

		# If no patch was generated, the file is either "same" or "clean".
		$pNew eq 'none' and next;

		# However, an empty $pNew indicates an error. (check_tree() has it reported already.)
		length($pNew) or return 0;

		# This is in order
		$hFixedPatches{$pNew} = 1;

		# If we are here, transfer the file line. It is useful.
		$line =~ s/$src/$real/ms;
		push @lOut, $line;
	}  ## End of scanning lines

	if ( 0 == scalar keys %hFixedPatches ) {
		unlink $pFile;  ## Empty patch...
		return -1;
	}

	# Load all generated patches and add them to lOut
	# ----------------------------------------------------------
	for my $pNew ( keys %hFixedPatches ) {
		$hFixedPatches{$pNew} or next;  ## Already handled

		if ( open my $fIn, '<', $pNew ) {
			my @lNew = <$fIn>;
			close($fIn) or croak("Closing $pNew FAILED: $!\n");
			chomp(@lNew);
			push @lOut, @lNew;
			unlink $pNew;
		} elsif ( -f $pNew ) {
			print "\nERROR [rework]: Can't open $pNew for reading!\n$!\n";
			return 0;
		}

		$hFixedPatches{$pNew} = 0;
	} ## end for my $pNew ( keys %hFixedPatches)

	# Store the patch commit for later reference
	# ----------------------------------------------------------
	$hSrcCommits{$pFile} = $commit;

	# Eventually overwrite $pFile with @lOut
	# ----------------------------------------------------------
	if ( open( my $fOut, '>', $pFile ) ) {
		print $fOut join( "\n", @lOut ) . "\n";
		close($fOut) or croak("Closing $pFile FAILED: $!\n");
	} else {
		print "\nERROR: Can not open $pFile for writing!\n$!\n";
		return 0;
	}

	return 1;
} ## end sub rework_patch

# --------------------------------------------
# --- Write back %hMutuals to $COMMIT_FILE ---
# --------------------------------------------
sub set_last_mutual {

	# Don't do anything if we haven't finished reading the commit file:
	$commits_read or return 1;

	my $out_text = "# Automatically generated commit information\n" . "# Only edit if you know what these do!\n\n";
	my ( $pLen, $rLen, $mLen, $sLen ) = ( 0, 0, 0, 0 );  # Length for the fmt

	# First we need a length to set all fields to.
	# ---------------------------------------------------------------
	# (And build a shortcut while at it so we do ...
	for my $path ( sort keys %hMutuals ) {
		length($path) > $pLen and $pLen = length($path);
		for my $refid ( sort keys %{ $hMutuals{$path} } ) {
			my $hM = $hMutuals{$path}{$refid};  # Shortcut!
			length($refid) > $rLen          and $rLen = length($refid);
			length( $hM->{mutual} ) > $mLen and $mLen = length( $hM->{mutual} );
			defined( $hM->{src} )           and ( length( $hM->{src} ) > 4 ) and $hM->{src} = 'src-' . $hM->{src}
			  or $hM->{src} = 'x';
			length( $hM->{src} ) > $sLen and $sLen = length( $hM->{src} );
			defined( $hM->{tgt} ) and ( length( $hM->{tgt} ) > 4 ) and $hM->{tgt} = 'tgt-' . $hM->{tgt}
			  or $hM->{tgt} = 'x';
		} ## end for my $refid ( sort keys...)
	} ## end for my $path ( sort keys...)

	# Now we can build the fmt
	my $out_fmt = sprintf( "%%-%ds %%-%ds %%-%ds %%-%ds %%s\n", $pLen, $rLen, $mLen, $sLen );

	# Second we build the out text
	# ---------------------------------------------------------------
	for my $path ( sort keys %hMutuals ) {
		for my $refid ( sort keys %{ $hMutuals{$path} } ) {
			my $hM = $hMutuals{$path}{$refid};  # Shortcut!
			$out_text .= sprintf( $out_fmt, $path, $refid, $hM->{mutual}, $hM->{src}, $hM->{tgt} );
		}
	} ## end for my $path ( sort keys...)

	# Third, write a new $COMMIT_FILE
	# ---------------------------------------------------------------
	if ( open( my $fOut, '>', $COMMIT_FILE ) ) {
		print $fOut $out_text;
		close($fOut) or croak("Closing $COMMIT_FILE FAILED: $!\n");
	} else {
		print "ERROR: Can not open $COMMIT_FILE for writing!\n$!\n";
		print "The content would have been:\n" . ( $DASH x 24 ) . "\n$out_text" . ( $DASH x 24 ) . "\n";
		exit 1;
	}

	return 1;
} ## end sub set_last_mutual

# -------------------------------------------------------------------------
# --- Take DIR and REFID and return the shortest possible REFID in DIR. ---
# -------------------------------------------------------------------------
sub shorten_refid {
	my ( $p, $r ) = @_;

	defined($p) and length($p) or croak('shorten_refid() called with undef path!');
	defined($r) and length($r) or croak('shorten_refid() called with undef refid!');

	#@type Git::Wrapper
	my $git    = Git::Wrapper->new($p);
	my @lOut   = ();
	my $result = 1;

	# Get the shortest possible $r (REFID)
	try {
		@lOut = $git->rev_parse( { short => 1 }, "$r" );
	} catch {
		print "ERROR: Couldn't rev-parse ${p}::${r}\n";
		print 'Exit Code : ' . $_->status . "\n";
		print 'Message   : ' . $_->error . "\n";
		$result = 0;
	};
	$result and return $lOut[0];
	return $EMPTY;
} ## end sub shorten_refid

# Helper to show the argument as a non permanent progress line.
sub show_prg {
	my ($msg) = @_;
	my $len = length($prg_line);

	$len and print "\r" . ( $SPACE x $len ) . "\r";

	$prg_line = $msg;

	if ( length($prg_line) > 0 ) {
		local $| = 1;
		print $msg;
	}

	return 1;
} ## end sub show_prg

# Callback function for File::Find
sub wanted {
	my $f = $File::Find::name;

	( $f   =~ m/[.]pwx$/ms )    or  ## .pwx files must not be considered, they are strictly temporary
	  ( $f =~ m,man/rules/,ms ) or  ## the man page generation rules are generated and must not be touched
	  return add_source_file($f);

	return 1;
} ## end sub wanted
