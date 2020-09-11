#!/usr/bin/perl

# ================================================================
# ===        ==> --------     HISTORY      -------- <==        ===
# ================================================================
#
# Version  Date        Maintainer      Changes, Additions, Fixes
# 0.0.1    2017-04-08  sed, PrydeWorX  First basic design
#
# ========================
# === Little TODO list ===
# ========================
#
# * Nothing right now
#
# ------------------------
use strict;
use warnings FATAL => 'all';
use Cwd qw(getcwd abs_path);
use File::Basename;
use File::Find;
use Readonly;

# ================================================================
# ===        ==> ------ Help Text and Version ----- <==        ===
# ================================================================
Readonly my $VERSION => "0.0.1"; ## Please keep this current!
Readonly my $VERSMIN => "-" x length( $VERSION );
Readonly my $PROGNAME => basename( $0 );
Readonly my $USAGE_SHORT => "$PROGNAME [-h|--help]";
Readonly my $USAGE_LONG => qq#
Orphaned file finder V$VERSION
----------------------$VERSMIN

    Search the current tree, from where this program is called, for meson.build,
    header and source files. Then check all headers and source files whether
    they are somehow included in the build, and report all those that seem to
    be orphaned.

Usage :
-------
  $USAGE_SHORT

  The program takes the directory from where it is called as the root directory
  from where to search. This should be the directory where the meson_options.txt
  and root meson.build files are stored.

Options :
---------
    -h|--help           | Print this help text and exit.
#;

# ================================================================
# ===        ==> -------- Global variables -------- <==        ===
# ================================================================
my $file_fmt    = ""; ## Format string built from the longest file name in generate_file_list().
my $main_result = 1;  ## Used for parse_args() only, as simple $result is local everywhere.
my $show_help   = 0;


# ================================================================
# ===        ==> ------- MAIN DATA STRUCTURES ------ <==       ===
# ================================================================
my %build_map = (); ## Map of the meson.build files
# The structure is:
# ( meson file =>
#   ( header/source : 0 if not present, -1 if in masked list only, 1 if in regular
#                     only, 2 if both in masked and regular list.
#   )
# )
my @build_files  = (); ## Final file list of meson.build files, generated in in generate_file_list().
my @header_files = (); ## Final file list of header files, generated in in generate_file_list().
my %include_map  = (); ## Map of all includes that the found files are having and are used in.
# The structure is:
# ( file => (must be basename)
#   ( built_by    : name of the meson.build file this file is used in, or undef if none.
#     included_by => : Map of files including this file for easier access and analysis
#     ( file : 1 on finding, 0 if it became irrelevant )
#     included_in : Number of valid include statements found this file is in.
#     includes    : Map of files this file includes
#     is_header   : 1 if .h* file, otherwise 0,
#     file_path   : full (relative) path to the file
#   )
my %known_files = (); ## Used to tick down all files that are actually in the src tree
my %orphans     = (); ## As we loop the header analysis, we have to collect our findings first.
# file => 1 source file not built, 2 header not included, 3 header also listed in a build file
my @source_files = (); ## Final file list of source files, generated in in generate_file_list().


# ================================================================
# ===        ==> --------  Function list   -------- <==        ===
# ================================================================
sub generate_build_map;   ## Goes through the build file list and fills %build_map
sub generate_file_list;   ## Find all relevant files and store them in the @*_files lists
sub generate_include_map; ## Goes through the header and source file lists and fills the %include_map
sub invalidate_includes;  ## Go through the map and invalidate one files includes
sub parse_args;           ## Parse ARGV for the options we support
sub wanted;               ## Callback function for File::Find


# ================================================================
# ===        ==> --------    Prechecks     -------- <==        ==
# ================================================================

$main_result = parse_args( @ARGV );
( ( !$main_result ) ## Note: Error or --help given, then exit.
	  or ( $show_help and print "$USAGE_LONG" ) ) and exit( !$main_result );
generate_file_list or exit 1;
generate_build_map or exit 1;
generate_include_map or exit 1;


# ================================================================
# ===        ==> -------- = MAIN PROGRAM = -------- <==        ===
# ================================================================

# The first step is to go through all source files that have
# no build file assiciation, and invalidate their including.
# --------------------------------------------------------------
for my $bn ( sort keys %include_map ) {

	$include_map{ $bn }{ is_header } and next;           ## later...
	defined( $include_map{ $bn }{ built_by } ) and next; ## this file is needed

	# invalidate its includes
	invalidate_includes( $bn );

	# This file is an orphan, so add it if it actually exists
	defined( $known_files{ $bn } ) and $orphans{ $bn } = 1;
} ## end of searching for orphaned source files

# The second step is to go through all header files, and search
# for any that aren't included anywhere, invalidate their
# includes, and report if they are part of a build file when
# they shouldn't. Repeat this until no changes are found.
# --------------------------------------------------------------
my $have_change = 1;
my %invalidated = (); ## Tick off what wen through invalidate_includes()
while ( 1 == $have_change ) {
	$have_change = 0;
	for my $bn ( sort keys %include_map ) {

		$include_map{ $bn }{ is_header } or next;        ## source files already handled
		$include_map{ $bn }{ included_in } > 0 and next; ## Not interesting (yet)
		defined( $invalidated{ $bn } ) and next;             ## Already handled

		# So the file is nowhere included, and not recorded, if we are here.
		$have_change = 1;

		# Like with the source files above, go through the includes and invalidate them
		invalidate_includes( $bn );
		$invalidated{ $bn } = 1;

		# Only add to %orphans what actually exists
		defined( $known_files{ $bn } ) or next;
		defined( $include_map{ $bn }{ built_by } )
			  and $orphans{ $bn } = 3
			  or $orphans{ $bn }  = 2;

	}
}

# ===========================
# === END OF MAIN PROGRAM ===
# ===========================

END {
	if ( 0 == $show_help ) {

		# In any case, but showing help, print out the orphan list
		scalar keys %orphans
			  and print "\nThe orphans have been found:\n================\n"
			  or print "\nNo orphans were found\n";
		for my $status ( 1 .. 3 ) {
			1 == $status and print( " 1) These source files are not built:\n----------------\n" );
			2 == $status and print( " 2) These headers are nowhere included:\n----------------\n" );
			3 == $status and print( " 3) These headers are also listed in build files:\n----------------\n" );
			for my $fn ( sort keys %orphans ) {
				$orphans{ $fn } == $status or next;
				my $fp = $include_map{ $fn }{ file_path };
				"unknown" eq $fp and next;
				$status < 3
					  and printf( " - $file_fmt\n", $fp )
					  or printf( " - $file_fmt -> %s\n", $fp, $include_map{ $fn }{ built_by } );
			}
		}
		# Let's print out all includes that are needed, and listed in the original
		# masked build list in, but not in the shortened elogind list.
		my %build_missing = ();
		for my $fn ( sort keys %include_map ) {
			defined( $known_files{ $fn } ) or next;
			if ( ( $include_map{ $fn }{ included_in } > 0 )
				  && !defined( $include_map{ $fn }{ built_by } ) ) {
				my $mf = "_unknown";
				for my $bf ( keys %build_map ) {
					defined( $build_map{ $bf }{ $fn } ) and $mf = $bf and last;
				}
				$build_missing{ $mf }{ $fn } = 1;
			}
		}
		scalar keys %build_missing and print "\nNeeded headers not in build lists:\n================\n";
		for my $bf ( sort keys %build_missing ) {
			"_unknown" eq $bf
				  and print " - Not in any build file at all :\n"
				  or print " - $bf :\n";
			for my $fn ( sort keys %{$build_missing{$bf}} ) {
				print "   * $fn\n";
			}
		}
	} ## not showing help
}         ## end END

# ================================================================
# ===        ==> ---- Function Implementations ---- <==        ===
# ================================================================

# -----------------------------------------------------------------------
# --- Goes through the file list and fills %build_map                 ---
# --- Addidtionally the information found is used to pre-fill the     ---
# ---   %include_map                                                  ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub generate_build_map {
	my $bn; ## basename
	my $fp; ## filepath
	my $is_header = 0;
	my $is_masked = 0;
	my @lines     = ();

	foreach my $bf ( @build_files ) {
		if ( open( my $fIn, "<", $bf ) ) {
			@lines = <$fIn>;
			close( $fIn );
		} else {
			print "ERROR: $bf could not be opened for reading: $!\n";
			return 0;
		}

		# Go through all lines and search for source and header files
		foreach my $line ( @lines ) {
			chomp $line;
			$fp = "";

			$line =~ m/^#?\s*(\S+\.[hc](?:pp|xx)?)\s?$/ and $fp = $1;
			$line =~ m/'(\S+\.[hc](?:pp|xx)?)'/ and $fp         = $1;

			length( $fp ) or next;

			$line =~ m/^\s*#/ and $is_masked  = 1 or $is_masked = 0;
			$fp =~ m/\.h[^.]*/ and $is_header = 1 or $is_header = 0;

			# Get the basename path, but "enhance" the filepath if fp is already
			# the basename. (Which will be like that in most of the cases)
			$bn                = basename( $fp );
			$bn eq $fp and $fp = dirname( $bf ) . "/" . $fp;

			# Initialize entry if needed
			defined( $build_map{ $bf }{ $bn } ) or $build_map{ $bf }{ $bn } = 0;

			# Record our findings in the build map
			$is_masked and ( (
				  ( ( 0 < $build_map{ $bf }{ $bn } ) and $build_map{ $bf }{ $bn } = 2 )
					    or $build_map{ $bf }{ $bn }                           = -1
			) or (
				  ( ( 0 > $build_map{ $bf }{ $bn } ) and $build_map{ $bf }{ $bn } = 2 )
					    or $build_map{ $bf }{ $bn }                           = 1
			) );

			# Pre-fill the include map if this entry is not masked
			$is_masked and next;
			defined( $include_map{ $bn } ) or $include_map{ $bn } = {
				  built_by    => $bf,
				  included_by => {},
				  included_in => 0,
				  includes    => {},
				  is_header   => $is_header,
				  file_path   => $fp
			};
		} ## End of scanning lines
	}         ## End of foreach @build_files

	return 1;
}


# -----------------------------------------------------------------------
# --- Finds all relevant files and store them in @wanted_files        ---
# --- Returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub generate_file_list {

	# Do some cleanup first. Just to be sure.
	`rm -rf build`;
	`find -iname '*.orig' -or -iname '*.bak' -or -iname '*.rej' -or -iname '*~' -or -iname '*.gc??' | xargs rm -f`;

	# Add the root meson.build file first
	if ( -f "meson.build" ) {
		find( \&wanted, "meson.build" );
	}

	# Add the src dir, that's where everything happens
	if ( -d "src" ) {
		find( \&wanted, "src" );
	}

	# Just to be sure...
	scalar @build_files
		  or print( "ERROR: No build files found? Where the hell are we?\n" )
		  and return 0;
	scalar @header_files
		  or print( "ERROR: No header files found? Where the hell are we?\n" )
		  and return 0;
	scalar @source_files
		  or print( "ERROR: No source files found? Where the hell are we?\n" )
		  and return 0;

	# Get the maximum file length and build $file_fmt
	my $mlen = 0;
	for my $f ( @source_files, @header_files, @build_files ) {
		length( $f ) > $mlen and $mlen = length( $f );
	}
	$file_fmt = sprintf( "%%-%d%s", $mlen, "s" );

	return 1;
} ## end sub generate_file_list


# -----------------------------------------------------------------------
# --- Goes through the header and source file lists and fills the     ---
# ---   %include_map                                                  ---
# --- returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub generate_include_map {
	my $bn; ## basename
	my $fp; ## file path
	my $if; ## include file
	my $is_header;
	my @lines = ();

	# Scan source and header files
	foreach my $sf ( @source_files, @header_files ) {

		$bn = basename( $sf );
		$sf =~ m/\.h[^.]*/
			  and $is_header = 1
			  or $is_header  = 0;

		# Init the map entry, if this file was not found in and meson.build file
		defined( $include_map{ $bn } ) or $include_map{ $bn } = {
			  built_by    => undef,
			  included_by => {},
			  included_in => 0,
			  includes    => {},
			  is_header   => $is_header,
			  file_path   => $sf
		};

		# Leech the file so we can check it
		if ( open( my $fIn, "<", $sf ) ) {
			@lines = <$fIn>;
			close( $fIn );
		} else {
			print "ERROR: $sf could not be opened for reading: $!\n";
			return 0;
		}

		# Now search for include statements that use double quotation marks
		for my $line ( @lines ) {
			chomp $line;
			$line =~ m/^\s*#include\s+\"([^"]+)\"/ and $fp = $1 or $fp = "";
			length( $fp ) or next;
			$if                = basename( $fp );
			$if eq $fp and $fp = "unknown";

			# Init the map entry, if this file was not handled, yet
			defined( $include_map{ $if } ) or $include_map{ $if } = {
				  built_by    => undef,
				  included_by => {},
				  included_in => 0,
				  includes    => {},
				  is_header   => 1,
				  file_path   => $fp
			};

			# Add this file to the scanned file entry
			$include_map{ $bn }{ includes }{ $if } = 1;
			if ( !defined( $include_map{ $if }{ included_by }{ $bn } ) ) {
				$include_map{ $if }{ included_by }{ $bn } = 1;
				$include_map{ $if }{ included_in }        += 1;
			}
		} ## End of scanning source file
	}         ## End of checking source and header files

	return 1;
}


# -----------------------------------------------------------------------
# --- Go through the map and invalidate the arguments includes        ---
# --- returns 1 on success, 0 otherwise.                              ---
# -----------------------------------------------------------------------
sub invalidate_includes {
	my ( $sf ) = @_;
	foreach my $fn ( keys %{$include_map{ $sf }{ includes }} ) {
		defined( $include_map{ $fn } ) or next;
		if ( defined( $include_map{ $fn }{ included_by }{ $sf } )
			  && ( $include_map{ $fn }{ included_by }{ $sf } > 0 ) ) {
			$include_map{ $fn }{ included_by }{ $sf } = 0;
			$include_map{ $fn }{ included_in }        -= 1;
		}
	}

	return 1;
}


# -----------------------------------------------------------------------
# --- parse the given list for arguments.                             ---
# --- returns 1 on success, 0 otherwise.                              ---
# --- sets global $show_help to 1 if the long help should be printed. ---
# -----------------------------------------------------------------------
sub parse_args {
	my @args   = @_;
	my $result = 1;

	for ( my $i = 0; $i < @args; ++$i ) {

		# Check for -h|--help option
		# -------------------------------------------------------------------------------
		if ( $args[$i] =~ m/^-(?:h|-help)$/ ) {
			$show_help = 1;
		}

		# Check for unknown options:
		# -------------------------------------------------------------------------------
		elsif ( $args[$i] =~ m/^-/ ) {
			print "ERROR: Unknown option \"$args[$1]\" encountered!\n\nUsage: $USAGE_SHORT\n";
			$result = 0;
		}

	} ## End looping arguments

	return $result;
} ## parse_srgs() end

# Callback function for File::Find
sub wanted {

	-f $_
		  and ( ( ( $_ =~ m/\.c(?:pp|xx)?$/ ) and push @source_files, $File::Find::name )
		     or ( ( $_ =~ m/\.h(?:pp|xx)?$/ ) and push @header_files, $File::Find::name )
		     or ( ( $_ =~ m/meson\.build$/ )  and push @build_files,  $File::Find::name ) )
		  and $known_files{ basename( $_ ) } = 1;

	return 1;
} ## end sub wanted
