#!/usr/bin/perl -w

# ================================================================
# ===        ==> --------     HISTORY      -------- <==        ===
# ================================================================
#
# Version  Date        Maintainer      Changes, Additions, Fixes
# 0.0.1    2017-03-12  sed, PrydeWorX  First basic design
# 0.1.0    2019-02-18  sed, PrydeWorX  Fixed typo; PO files are now first restored before reworking them.
# 0.2.0    2019-02-25  sed, PrydeWorX  Make sure that files with non-existent extensions are found.
# 0.3.0    2019-02-26  sed, PrydeWorX  - Fix file references in po files, if the reference is wrong.
#                                      - Fix duplication of empty lines when calling update_po_files.pl more than once.
#
# ========================
# === Little TODO list ===
# ========================
#
use strict;
use warnings;
use Cwd qw(getcwd abs_path);
use File::Basename;
use File::Find;
use Readonly;

# ================================================================
# ===        ==> ------ Help Text and Version ----- <==        ===
# ================================================================
Readonly my $VERSION     => "0.3.0"; ## Please keep this current!
Readonly my $VERSMIN     => "-" x length($VERSION);
Readonly my $PROGDIR     => dirname($0);
Readonly my $PROGNAME    => basename($0);
Readonly my $WORKDIR     => getcwd();
Readonly my $USAGE_SHORT => "$PROGNAME <--help|path to po directory>";
Readonly my $USAGE_LONG  => qq#
elogind po file cleaner V$VERSION
-------------------------$VERSMIN

    Check all .po files in the given directory and comment out all lines
    that refer to non-existent files.

Usage :
-------
  $USAGE_SHORT

Options :
---------
    -h|--help           | Print this help text and exit.
#;

# ================================================================
# ===        ==> -------- Global variables -------- <==        ===
# ================================================================

my $file_fmt     = ""; ## Format string built from the longest file name in generate_file_list().
my $main_result  = 1;  ## Used for parse_args() only, as simple $result is local everywhere.
my $po_file_path = ""; ## Path to where the .po files are to be found.
my $show_help    = 0;
my @source_files = (); ## File list generated by generate_file_list()

# ================================================================
# ===        ==> --------  Function list   -------- <==        ===
# ================================================================

sub generate_file_list; ## Find all relevant files and store them in @wanted_files
sub parse_args;         ## Parse ARGV for the options we support
sub wanted;             ## Callback function for File::Find

# ================================================================
# ===        ==> --------    Prechecks     -------- <==        ==
# ================================================================

$main_result = parse_args(@ARGV);
( (!$main_result)                 ## Note: Error or --help given, then exit.
	or ( $show_help and print "$USAGE_LONG" ) )
	and exit(!$main_result);
generate_file_list or exit 1;

# ================================================================
# ===        ==> -------- = MAIN PROGRAM = -------- <==        ===
# ================================================================

for my $pofile (@source_files) {
	printf("$file_fmt: ", $pofile);

	# --- 1) Load the file ---
	# ------------------------
	my @lIn = ();
	if (open(my $fIn, "<", $pofile)) {
		@lIn = <$fIn>;
		close($fIn);
	} else {
		print "ERROR READING: $!\n";
		next;
	}

	# --- 2) Remove all masks from the input line, we are regenerating them ---
	# -------------------------------------------------------------------------
	my @lPo       = ();
	my $in_block  = 0; ## 1 if in commented out block

	for my $line (@lIn) {
		chomp $line;

		if ( $line =~ m/^#if 0/ ) {
			$in_block = 1;
		} elsif ($line =~ m/^#endif/) {
			$in_block = 0;
		} else {
			$in_block and $line =~ s/^#(?: )?//;
			push @lPo, $line;
		}
	}

	# --- 3) Copy @lIn to @lOut, commenting out all parts ---
	# ---    belonging to files that do not exist.        ---
	# -------------------------------------------------------
	my $count     = 0;
	my @lOut      = ();
	my $was_block = 0; ## save in_block, so we know when to add elogind masks

	$in_block = 0; ## reset

	for my $line (@lPo) {

		# in_block switches are done on file identifications lines, which look like
		# this : "#: ../src/import/org.freedesktop.import1.policy.in.h:2"
		if ($line =~ m/^#:\s+([^:]+):\d+/) {

			# Note: There might be two file references, if the translated text spans
			#       more than one line. The second path is the same as the first, so
			#       it is sufficient not to end the regex with '$' here.
			my $f_ref   = $1;
			my $f_name  = basename($f_ref);
			my $f_dir   = dirname($f_ref);
			my $f_found;

			# The directory sometimes starts with "../" and sometimes without. As we
			# are looking from the po file path, as that is the point from where we
			# go relative, the "../" is important and must not be missing for us.
			($f_dir =~ m,^\.\./,) || ($f_dir = "../" . $f_dir);
			my $f_full = $po_file_path . "/" . $f_dir . "/" . $f_name;
			my ($f_no_h, $f_no_in) = ($f_full, $f_full);

			# Interestingly the policy files are listed as "policy.in.h", no matter how
			# they are really named. So while there is org.freedesktop.login1.policy,
			# it is listed as org.freedesktop.login1.policy.in.h
			# But annoyngly the '.h' is missing in some files, and sometimes even both
			# are missing.
			$f_no_h  =~ s/\.h$//;
			$f_no_in =~ s/\.in\.h$//;

			# Now see which file can be found.
			$f_found = -f $f_ref ? $f_ref
			         : -f $f_full ? $f_full
			         : -f $f_no_h ? $f_no_h
			         : -f $f_no_in ? $f_no_in : "";

			$was_block  = $in_block;
			$in_block   = length($f_found) ? 0 : 1;
			$in_block and ++$count;

			# If the listed reference is wrong, fix it.
			if (length($f_found)) {
				$f_found =~ s,^$po_file_path/,,; ## That must be removed again
				($f_ref ne $f_found) and $line =~ s,$f_ref,$f_found,g;
			}
		}

		# If the in_block switches, add elogind mask start or end
		if ($was_block != $in_block) {
			if ($was_block) {
				my $eIdx = scalar @lOut - 1;
				"#" eq $lOut[$eIdx]
					and $lOut[$eIdx] = "#endif // 0"
					 or push(@lOut, "#endif // 0");
				## Add an empty line in any case
				push(@lOut, "");
			} else {
				push(@lOut, "#if 0 /// UNNEEDED by elogind");
			}
			$was_block = $in_block;
		}

		# If we are in block, comment out the line:
		if ($in_block) {
			length($line)
				and $line = "# $line"
				 or $line = "#";
		}

		# Now push the line, it is ready.
		push(@lOut, $line);

	} ## End of line copying

	# Make sure to end the last block
	$in_block and push(@lOut, "#endif // 0");

	# --- 4) Overwrite the input file with the adapted text. ---
	# ----------------------------------------------------------
	if (open(my $fOut, ">", $pofile)) {
		for my $line (@lOut) {
			print $fOut "$line\n";
		}
		close($fOut);
		print "$count blocks masked\n";
	} else {
		print "ERROR WRITING: $!\n";
	}
} ## End of main loop

# ===========================
# === END OF MAIN PROGRAM ===
# ===========================

# ================================================================
# ===        ==> ---- Function Implementations ---- <==        ===
# ================================================================

# -----------------------------------------------------------------------
# --- Finds all relevant files and store them in @wanted_files        ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub generate_file_list {

	# Use File::Find to search for .po files:
	find(\&wanted, "$po_file_path");

	# Just to be sure...
	scalar @source_files
		 or print("ERROR: No source files found? Where the hell are we?\n")
		and return 0;

	# Get the maximum file length and build $file_fmt
	my $mlen = 0;
	for my $f (@source_files) {
		length($f) > $mlen and $mlen = length($f);
	}
	$file_fmt = sprintf("%%-%d%s", $mlen, "s");

	return 1;
}

# -----------------------------------------------------------------------
# --- parse the given list for arguments.                             ---
# --- returns 1 on success, 0 otherwise.                              ---
# --- sets global $show_help to 1 if the long help should be printed. ---
# -----------------------------------------------------------------------
sub parse_args {
	my @args      = @_;
	my $result    = 1;

	for (my $i = 0; $i < @args; ++$i) {

		# Check for -h|--help option
		# -------------------------------------------------------------------------------
		if ($args[$i] =~ m/^-(?:h|-help)$/) {
			$show_help = 1;
		}

		# Check for unknown options:
		# -------------------------------------------------------------------------------
		elsif ($args[$i] =~ m/^-/) {
			print "ERROR: Unknown option \"$args[$1]\" encountered!\n\nUsage: $USAGE_SHORT\n";
			$result = 0;
		}

		# Everything else is considered to the path to the .po files
		# -------------------------------------------------------------------------------
		else {
			# But only if it is not set, yet:
			if (length($po_file_path)) {
				print "ERROR: Superfluous po file path \"$args[$i]\" found!\n\nUsage: $USAGE_SHORT\n";
				$result = 0;
				next;
			}
			if ( ! -d "$args[$i]") {
				print "ERROR: po file path \"$args[$i]\" does not exist!\n\nUsage: $USAGE_SHORT\n";
				$result = 0;
				next;
			}
			$po_file_path = $args[$i];
		}
	} ## End looping arguments

	# If we have no upstream path now, show short help.
	if ($result && !$show_help && !length($po_file_path)) {
		print "ERROR: Please provide a path to the po files!\n\nUsage: $USAGE_SHORT\n";
		$result = 0;
	}

	return $result;
} ## parse_srgs() end

# Callback function for File::Find
sub wanted {
	-f $_ and ($_ =~ m/\.po$/ )
	      and push @source_files, $File::Find::name;
	return 1;
}
