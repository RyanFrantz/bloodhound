#!/usr/bin/perl

#
# bloodhound - Scan a given directory for new files and notfiy appropriately -ryanfrantz 1/30/2007
#

use warnings;
use strict;

use Sys::Hostname;
use File::Basename;
use File::Copy;
use Net::SMTP;
use Config::Simple;
use Sys::Syslog;
use GnuPG::Interface;
use IO::File;
use IO::Handle;
use DBI;
use Archive::Zip qw( :ERROR_CODES :CONSTANTS );	# see 'http://search.cpan.org/~adamk/Archive-Zip-1.23/lib/Archive/Zip.pm' for more info
use File::Path 'mkpath';

use lib "/usr/local/bloodhound/lib";	# explicitly specify the location of bloodhound-specific libraries
use Bloodhound::Config;	# import some variables ($gpgbin, $secretkey, $passphrase, $sqlHost, $database, $sqlUsername, $sqlPassword, $debug)

# TODO
# 1. Complain to somebody when a config parameter is missing (i.e. email address) instead of letting the program throw
# an error for cron to relay

#
# variables
#
# directories and files...
my $baseDir = "/usr/home/sftp/";  # Note the trailing slash; leave it in there...
my $dogHouse = "/usr/local/bloodhound";
my $logDir = $dogHouse . "/logs";
my $logFile = $logDir . "/bloodhound.log";
my $cfgDir = $dogHouse . "/etc";
my $emailCfg = $cfgDir . "/email.cfg";

# time-related stuff...
my $startTime = time;
my $humanTime = localtime;
my $savedTime;
my $savedTimeFile = $cfgDir . "/savedTime";
# $runInterval will be used to perform "lookbacks" instead of "> $time2Compare"; this should capture "new" files much better
my $runInterval = 5 * 60;	# 5 minutes in seconds (300); adjust this if bloodhound's frequency/schedule changes
my $timingSafetyNet = 5;	# 5 seconds; sometimes bloodhound doesn't start _exactly_ on the minute (i.e. 15:05:02, 20:25:03); be sure we cover/overlap an extra few seconds
$runInterval += $timingSafetyNet;	# combine the two
my $nowMinusRunInterval;	# instantiate for later

# for syslog
my $identity = basename( $0 );	# this should be 'bloodhound'
my $syslogOptions = 'pid';	# log the PID of the running process
my $facility = 'daemon';	# we're not quite a daemon... yet

# miscellaneous...
my $doze = '1'; # time to sleep...
my $whoami = hostname;
my $programName = basename $0;
my $zipErrorOutput;	# errors sent to our zip error handler, zipErrorHandler()

# hash the files using the file _disposition_ as the key; each value is a key (account name) to an arrayref of files
# NOTE: the prior version of bloodhound indexed by 'direction'; I've expanded on that concept here through the use of 'disposition'
# Data Structure:
# %account2Files => {
#		IN	=>	{
#				account1	=>	[files],
#				account2	=>	[files],
#			},
#		OUT	=>	{
#				account1	=>	[files],
#				account3	=>	[files],
#			},
#		UNKNOWN	=>	{
#				accountX	=>	[files],
#			},
# };
#
# File Disposition types:
# IN									= new inbound file, unprocessed
# OUT									= new outbound file (unused in the internal version of bloodhound); notify external account
# UNKNOWN							= new file that doesn't belong anywhere (i.e. written to non-standard location); notify someone
# QUEUED						 	= file found in the queue, waiting to be processed
# PROCESSING_SUCCESS	= file (originally new or queued) that has been processed successfully; notify someone
# PROCESSING_FAILURE 	= file (originally new or queued) that has _not_ been processed successfully; notify someone
my %account2Files;	# finally! we declare the hash...

# database-related items (pulled via Bloodhound::Config but can be overridden by un-commenting them here)
#my $sqlHost = '';	# FQDN of SQL Server host
#my $database = '';	# database name
#my $sqlUsername = '';	# local, SQL Server user
#my $sqlPassword = '';	# should probably hide this away somewhere...
#my $debug ='';		# do we want debug messages in the system log?

my $filesMovedFlag = '0';	# ProdEngine.spProcessQueueFiles needs to know the files _haven't_ been moved yet; we're just trying to find out where they go
my $userID = $sqlUsername;	# make this the same as the user name we log into SQL Server with
my $dbh;	# declare this for later...

#
# subs (hoagies and grinders, hoagies and grinders!)
#

sub logMsg {

	# log messages via syslog
	my $message = shift;
	my $priority = 'info';  # should probably make this an option later...

	syslog( $priority, $message );

}	# end logMsg()

my %account2Email;
sub parseEmailCfg {

	# this creates a hash whose values may be a scalar or an arrayref depending on what it sees in the config file
	# CONFIG FILE:
	# [acme]
	# email = wcoyote@acme.com, rrunner@acme.com
	# accountID = 007
	#
	# HASH:
	# acme.email => [ wcoyote@acme.com, rrunner@acme.com ],
	# acme.accountID => '007',

  my $cfg = new Config::Simple( $emailCfg ) or die "ERROR parseEmailCfg(): " . Config::Simple->error . "\n";
  %account2Email = $cfg->vars();

}	# end parseEmailCfg

sub miniStat {

	# call stat() on the given file; just return the size, mtime, and ctime
	# expect one arg, the file name
	my $file = shift;
	my ( $size, $mtime, $ctime ) = ( stat $file )[7,9,10];	# an array slice of the list returned from the stat() call

	return $size, $mtime, $ctime;

}	# end miniStat()

sub findFiles {

	use File::Find;

	my ( $baseDir ) = @_;

	my ( $size, $mtime, $ctime );

	# let's tell File::Find how/what we want to find
	my $wanted = sub {
		# this coderef is technically a closure; look it up!
		if ( -f ) {

			return if /^\.+/;	# skip dot files (i.e. .bash_history)
			( $size, $mtime, $ctime ) = miniStat( $_ );
			my $fileDisposition = 'UNKNOWN';	# initialize to 'UNKNOWN' in the event we find something out of the ordinary...

			my $subDir = $File::Find::dir;
			$subDir =~ s/$baseDir//;	# strip out the base dir and leave the account name (and everything that trails)

			my $accountName = $subDir;	# copy the key to another variable to do work on it
			$accountName =~ s/\/.*$//;	# strip out everything after the account name (i.e. leave only 'ftp_acme')
			$accountName = 'NO_ACCOUNT' if $accountName eq '';	# assign some name in case we get an empty name

			my $fileName = $subDir . '/' . $_;	# File::Find sets $_ to the file name (no path); we'll end up with something like 'ftp_foobar/LIVE/inbound/...'

				$fileDisposition = 'IN' if $subDir =~ /inbound/;
				$fileDisposition = 'OUT' if $subDir =~ /outbound/;

				# make sure we check for queued files and set $fileDisposition _after_ checking 'in' vs 'out'
				$fileDisposition = 'PRODUCTIONQUEUE' if $subDir =~ /ProductionQueue/;
				$fileDisposition = 'UNKNOWNQUEUE' if $subDir =~ /UnknownQueue/;

				if ( $fileDisposition =~ /QUEUE/ ) {
					push @{ $account2Files{ $fileDisposition }{ $accountName } }, $fileName . ';' . $size . ';' . $mtime;
					logMsg( "FOUND IN QUEUE: $fileName | $size bytes | mtime: $mtime" ) if $debug;
					return;	# skip to the next file; no more processing required for queued files
				}

				# still updating?
				my $stillUpdating = check4Update( $File::Find::name, $size );	# see if the file is being updated...
				#my $fileName = $subDir . '/' . $_;	# File::Find sets $_ to the file name (no path); we'll end up with something like 'ftp_foobar/LIVE/inbound/...'
				if ( $stillUpdating eq 'NO' ) {	# the file has been transferred in full
					# send the file name to homogenize() to clean it up in case it contains non-standard characters or those that can be shell-interpreted down the line
					my ( $cleanStatus, $cleanedFilename, $filename2Clean ) = homogenize( $File::Find::name );       # we need the full path to the file
					if ( $cleanStatus eq 'SUCCESS' ) {
						logMsg( "HOMOGENIZE [SUCCESS]: $filename2Clean -> $cleanedFilename" );
						# strip $baseDir from $cleanedFilename to match the convention we use for logging
						$cleanedFilename =~ s/$baseDir//;
						# index the file name, size, and mod time; delimit the info with semi-colons
						push @{ $account2Files{ $fileDisposition }{ $accountName } }, $cleanedFilename . ';' . $size . ';' . $mtime;
						logMsg( "NEW: $cleanedFilename | $size bytes | mtime: $mtime" );
					} else {
						logMsg( "HOMOGENIZE [FAILED]: $filename2Clean -> $cleanStatus" );
						# index the file name, size, and mod time; delimit the info with semi-colons
						push @{ $account2Files{ $fileDisposition }{ $accountName } }, $fileName . ';' . $size . ';' . $mtime;
						logMsg( "NEW: $fileName | $size bytes | mtime: $mtime" );
					}	# end "if $cleanStatus eq 'HOMOGENIZE_SUCCESS'..."
				}	else {	# the file is still being transferred; log it
					logMsg( "NEW (UPDATING): $fileName | $size bytes | mtime: $mtime" );
				}	# end "if ( $stillUpdating eq 'NO'..."

			#}	# end "if ( $mtime..."

		}	# end "if ( -f )..."

	};	# end "my $wanted..."

	# find me some files, BOY!
	find( $wanted, $baseDir );

}	# end findFiles()

sub check4Update {

	my ( $file2Check, $initSize ) = @_;	# expect the file name to check and the initial reported size

	my ( $chkSize, $mtime, $ctime );  # init these for down below...
	my $updating; # this will be returned at some point to reflect an updating file; if no file, it's not updating, duh!

	sleep $doze;	# sleep for a wee bit...

	if ( -f $file2Check ) {
		#( $chkSize, $mtime, $ctime ) = ( stat( $file2Check ) )[7,9,10];
		( $chkSize, $mtime, $ctime ) = miniStat( $file2Check );
		#print "Size: $chkSize bytes \n";	# debug
		#print "mtime: $mtime => " . localtime( $mtime ) . "\n";	# debug
		#print "ctime: $ctime => " . localtime( $mtime ) . "\n";	# debug
	} else {
		#print "No such file: \'$file2Check\'!\n";	# debug
		$updating = undef;
		return $updating;
	}

	if ( $chkSize > $initSize ) {
		$updating = 'YES';
	} else {
		$updating = 'NO';
	}

	return $updating;

}	# end check4Update()

sub decryptFile {

	my ( $cipherFile ) = @_;

	# make sure the input file exists
	if ( ! -r $cipherFile ) {
		logMsg( "DECRYPT_ERROR: Invalid/unreadable input file [$cipherFile]" );
		return $cipherFile, 'DECRYPT_INVALID_FILE';
	}
	my $decryptedFile = $cipherFile;
	# strip the extension and be case-insenstive
	$decryptedFile =~ s/\.pgp|\.gpg|\.asc//i;

	my $gnupg = GnuPG::Interface->new();

	# create the handle objects we'll assign to GnuPG::Handles later
	my ( $input, $output, $error, $passphrase_fh, $status_fh ) = (
		IO::File->new( $cipherFile ),		# thanks to Michael Rash (gpgdir) for this tidbit
		IO::File->new( "> $decryptedFile" ),	# it works better than calling IO::Handle!
		IO::Handle->new(),
		IO::Handle->new(),
		IO::Handle->new(),
	);

	# create the appropriate GnuPG::Handles objects
	my $handles = GnuPG::Handles->new(
		stdin				=> $input,
		stdout			=> $output,
		stderr			=> $error,
		passphrase	=> $passphrase_fh,
		status			=> $status_fh,
	);

	# make sure we read/write directly to the input and output file handles to prevent any buffering issues with large files
	$handles->options( 'stdin' )->{ 'direct' } = 1;
	$handles->options( 'stdout' )->{ 'direct' } = 1;
	
	# open up communication with gpg and decrypt the file
	my $pid = $gnupg->decrypt(
		handles	=>	$handles,
	);

	# send the passphrase (from Bloodhound::Config) into the passphrase handle and close it
	print $passphrase_fh $passphrase;
	close $passphrase_fh;

	# read the error and status file handles for possible use later
	my @errors = <$error>;
	my @statusInfo = <$status_fh>;

	# need some better error handling, just in case
	# right now, logMsg() only expects scalars...
	#print "\nSTATUS: @statusInfo";	# debug
	#print "\nERROR: @errors";	# debug

	# clean up...
	close $input;
	close $output;
	close $error;
	close $status_fh;

	waitpid $pid, 0;	# wait for, and clean up the forked gpg process
	#print "\nRETURN STATUS: $?\n\n";	# debug

	# log an error if we created an empty file
	if ( -s $decryptedFile == 0 ) {
		logMsg( "DECRYPT ERROR: Created empty file! [$decryptedFile]" );
		logMsg( "DEBUG: Deleting empty file [$decryptedFile]" ) if $debug;
		unlink $decryptedFile;	# clean it up so it doesn't get processed on subsequent runs
		return $cipherFile, 'DECRYPT_EMPTY_FILE';
	}	# end "if ( -s $outFile == 0 )..."

	# let 'em know it's alright!
	return $cipherFile, 'FILE_DECRYPTED', $decryptedFile;

}	# end decryptFile()

sub homogenize {

	# homogenize() should 'clean' filenames of any 'improper' characters thay may have a negative
	# impact down the line (i.e. pipes, asterisks, etc.) and rename them accordingly; we want to de-taint our input

	# NOTE: this sub gets called on _all_ files; so even "clean" files get inspected

	# I could have created one monster regex for these matches but my intent was to clearly demonstrate
	# what I want to match and replace; it's also less monolithic this way (read modular)

	# ARGS: expect a file name as the sole argument
	my $filename2Clean = shift;	# should be the full path to the file
	my $fullPath = dirname( $filename2Clean );
	my $filename = basename( $filename2Clean );	# we only need the filename to operate on below
	my $cleanedFilename;	# placeholder for our cleaned filename

	# RETURN: $cleanStatus, $cleanedFilename, $filename2Clean

	return "NO_FILE_2_CLEAN" unless $filename2Clean;	# complain if we're called without an argument

	logMsg( "NEW [HOMOGENIZE]: $filename2Clean" );

	# replace whitespace with underscores globally; I *hate* whitespace in filenames
	( $cleanedFilename = $filename ) =~ s/\s+/_/g;	# copy and substitute at the same time

	$cleanedFilename =~ s/\|/_/g;			# replace pipes with underscores globally
	$cleanedFilename =~ s/\*/_/g;			# replace asterisks with underscores globally
	$cleanedFilename =~ s/;|:/_/g;		# replace semi-colons and colons with underscores globally
	$cleanedFilename =~ s/-/_/g;			# replace hyphens (i.e. command options) with underscores globally
	$cleanedFilename =~ s/\.\./_/g;		# replace double-dots (..) with underscores globally
	$cleanedFilename =~ s!/!_!g;			# replace forward slashes with underscores globally (using '!' to delimit statement)
	$cleanedFilename =~ s!\\!_!g;			# replace backward slashes with underscores globally (using '!' to delimit statement)
	$cleanedFilename =~ s/&/_/g;			# replace ampersands with underscores globally
	$cleanedFilename =~ s/@/_/g;			# replace 'at' symbols with underscores globally
	$cleanedFilename =~ s/!/_/g;			# replace exclamation points with underscores globally
	$cleanedFilename =~ s/\?/_/g;			# replace question marks with underscores globally
	$cleanedFilename =~ s/\[|\]/_/g;	# replace square brackets with underscores globally
	$cleanedFilename =~ s/{|}/_/g;		# replace curly brackets with underscores globally
	$cleanedFilename =~ s/\(|\)/_/g;		# replace parentheses with underscores globally
	$cleanedFilename =~ s/<|>/_/g;		# replace angle brackets with underscores globally
	$cleanedFilename =~ s/,/_/g;			# replace commas with underscores globally
	$cleanedFilename =~ s/~/_/g;			# replace tildes with underscores globally
	$cleanedFilename =~ s/`/_/g;			# replace backticks with underscores globally
	$cleanedFilename =~ s/'|"/_/g;		# replace single or double quotes with underscores globally
	$cleanedFilename =~ s/#/_/g;			# replace pound signs/hashes with underscores globally
	$cleanedFilename =~ s/\$/_/g;			# replace dollar signs with underscores globally
	$cleanedFilename =~ s/%/_/g;			# replace percent signs with underscores globally

	# final cleanup to keep files from containing many underscores (i.e. file___name.txt)
	$cleanedFilename =~ s/_+/_/g;			# replace multiple underscores with a single underscore globally

	# concatentate the cleaned filename with the original full path
	$cleanedFilename = $fullPath . '/' . $cleanedFilename;

	# rename the file; evaluate the expression to catch any errors
	eval { move( $filename2Clean, $cleanedFilename ) or die "$!" };

	if ( $@ ) {	# move failed; log it and continue on
		logMsg( "HOMOGENIZE [RENAME ERROR]: $filename2Clean -> $cleanedFilename [$@]" );
		return 'RENAME_ERROR', $cleanedFilename, $filename2Clean;
	} else {	# move succeeded; log it and push the file name and required stats
		logMsg( "HOMOGENIZE [RENAME SUCCESS]: $filename2Clean -> $cleanedFilename" );
	}	# end "if ( $@ )..." - test for move success

	return 'SUCCESS', $cleanedFilename, $filename2Clean;	# return status and both names for logging

}	# end homogenize()

sub getDBConnection {

	# open a database connection and return the handle
	# ARGS: $hostname, $database, $userName, $password
	my ( $hostname, $database, $userName, $password ) = @_;

	# we're going DSN-less!
	my $dsn = "driver={SQL Server};Server=$hostname; database=$database;uid=$userName;pwd=$password;";

	#my $dbh = DBI->connect( "DBI:ODBC:$dataSource", $userName, $password )
	my $dbh = DBI->connect( "DBI:ODBC:$dsn" )
 	 or die "Unable to connect to database using $dsn: " . DBI->errstr. "\n";

	return $dbh;

}	# end getDBConnection()

sub sqlQuery {

	# ARGS: expect the database handle, a SQL statement, and if required, bind variables (may be an arrayref)
	my ( $dbh, $sqlStatement, $sqlBindVars ) = @_;

	# return with error if we can't prepare the statement
	#my $sth_genericQuery = $dbh->prepare( $sqlStatement )
		#or die "sqlQuery() -> Unable to prepare statement \'$sqlStatement\': " . $dbh->errstr . "\n";
	my $sth_genericQuery;
	my $prepareRV;	# SQL preparation return value
	$prepareRV = $sth_genericQuery = $dbh->prepare( $sqlStatement );
	unless ( $prepareRV ) {
		return "PREPARE_ERROR: sqlQuery() -> Unable to prepare statement \'$sqlStatement\': " . $dbh->errstr;
	}	# end "unless ( $prepareRV )..."

	# return with error if we can't execute the statement
	my $executeRV;	# SQL execution return value
	if ( $sqlBindVars ) {

		# $sqlBindVars should be an arrayref if multiple bind variables were sent
		# NOTE: it's up to the caller to ensure the variables are in the correct order; there's no way to test against that
		if ( ref( $sqlBindVars ) eq 'ARRAY' ) {
			$executeRV = $sth_genericQuery->execute( @$sqlBindVars );	# deference the array
				#or die "sqlQuery() -> Unable to execute statement \'$sqlStatement\': " . $sth_genericQuery->errstr . "\n";
			unless ( $executeRV ) {
				return "EXECUTE_ERROR: sqlQuery() -> Unable to execute statement \'$sqlStatement\': " . $sth_genericQuery->errstr;
			}	# end "unless ( $executeRV )..."
		} else {
			$executeRV = $sth_genericQuery->execute( $sqlBindVars );	# it's just a simple scalar with a single variable
				#or die "sqlQuery() -> Unable to execute statement \'$sqlStatement\': " . $sth_genericQuery->errstr . "\n";
			unless ( $executeRV ) {
				return "EXECUTE_ERROR: sqlQuery() -> Unable to execute statement \'$sqlStatement\': " . $sth_genericQuery->errstr;
			}	# end "unless ( $executeRV )..."
		}	# end "if ( ref( $sqlBindVars..."

	} else {	# there are no bind variables
		$executeRV = $sth_genericQuery->execute();
			#or die "\n[ sqlQuery() ]\n-> Unable to execute statement \'$sqlStatement\': " . $sth_genericQuery->errstr . "\n";
		unless ( $executeRV ) {
			return "EXECUTE_ERROR: sqlQuery() -> Unable to execute statement \'$sqlStatement\': " . $sth_genericQuery->errstr;
		}	# end "unless ( $executeRV )..."
	}	# end "if ( $sqlBindVars..."

	my $results = $sth_genericQuery->fetchall_arrayref();
	if ( $sth_genericQuery->err() ) {
		return 'FETCH_ERROR: ' . $sth_genericQuery->errstr;
	} else {
		return $results;
	}	# end "if ( $sth_genericQuery->err()..."

}	# end sqlQuery()

sub getDSFilePath {

	# call 'ProdEngine.spProcessQueueFiles' to determine where new files should be placed
	# we expect the DB handle, 'filesMoved' flag, and a user ID/name to use for logging by the SP
	my ( $dbh, $filesMovedFlag, $userID ) = @_;

	my $sqlExecSP = qq( EXEC ProdEngine.spProcessQueueFiles
		\@FilesMoved = '$filesMovedFlag',
		\@UserId = '$userID'
	);	# end "my $sqlExecSP = ..."

	#print "\nsqlQuery( \$dbh, $sqlExecSP )\n\n";	# debug
	my $spResults = sqlQuery( $dbh, $sqlExecSP );

	if ( $spResults =~ 'ERROR' ) {
		logMsg( "getDSFilePath() ERROR: failed call -> sqlQuery( \$dbh, $sqlExecSP ) [VERBOSE: $spResults]" );
		return 'QUERY_ERROR';
	} else {	# send the results back
		return $spResults;	# this should be an arrayref of arrayrefs
	}	# end "if ( $spResults eq 'ERROR'..."

}	# end getDSFilePath()

sub getDSZipPassword {

	# call 'spDSProfileGetZipPassword' to look up a data source's ZIP password
	my ( $dbh, $accountName ) = @_;

	my $sqlExecSP = qq( EXEC spDSProfileGetZipPassword $accountName );

	#print "\nsqlQuery( \$dbh, $sqlExecSP )\n\n";   # debug
	my $spResults = sqlQuery( $dbh, $sqlExecSP );

	if ( $spResults =~ 'ERROR' ) {
		logMsg( "ERROR: getDSZipPassword() failed call -> sqlQuery( \$dbh, $sqlExecSP )" );	# this is critical enough to always log
		return "QUERY_ERROR";
	} else {        # send the results back
		return $spResults;
	}       # end "if ( $spResults eq 'ERROR'..."

}	# end getDSZipPassword()

sub copyFile2Repo {

	# copy the file to its intended destination
	my ( $src, $dest ) = @_;

	# create the directory if it doesn't exist; $destDir is the data source's current log number
	# make the destination path UNIXy so that dirname() can parse it (necessary 'magic' within Cygwin!)
	$dest =~ s!\\!\/!g;	# now looks like /dir1/dir2/file.txt
	my $destDir = dirname( $dest );
	#	$destDir =~ s!\/!\\!g;	# change all forward slashes to backslashes, globally (\dir1\dir2\file.txt)
	# I'm not sure why, but this next replacement made the UNC path look like '\\\host\dir1\dir2...'; commenting out - ryanfrantz 5/28/2008
	#$destDir =~ s!\\!\\\\!;	# make sure the first backslash is updated to be a double backslash to complete the UNC path (\\dir1\dir2\file.txt)
	logMsg( "DEBUG: [DESTINATION BASE == $destDir]" ) if $debug;
	if ( ! -d $destDir ) {
		logMsg( "DEBUG: MISSING [$destDir]" ) if $debug;
		logMsg( "DEBUG: MKPATH -> $destDir" ) if $debug;
		eval { mkpath( $destDir ); };
		#eval { mkpath( $destDir, { verbose => 1 } ); };	# debug
		if ( $@ ) {	# mkpath failed
			chomp $@;
			logMsg( "MKPATH ERROR [$@]" );	# this is crtical enough to always log
			return 'MKPATH ERROR', $destDir;
		} else {
			logMsg( "DEBUG: MKPATH SUCCESS [$destDir]" ) if $debug;
		}	# eval {mkpath}
	} else {
		logMsg( "DEBUG: DESTINATION EXISTS [$destDir]" ) if $debug;	# debug
	}	# end "if ( ! -d $destDir )..."

	# check the copy for success
	eval { copy( $src, $dest ) or die "$!" };

	if ( $@ ) {	# copy failed; log it and continue on
		logMsg( "$src -> $dest [COPY ERROR]: [$@]" );	# this is crtical enough to always log
		return 'COPY ERROR', $dest;
	} else {	# copy succeeded; log it and push the file name and required stats
		logMsg( "$src -> $dest [COPY SUCCESS]" );	# this is important enough to always log/track

		# remove the source file;
		eval { unlink $src or die "$!" };
		if ( $@ ) {	# unlink failed; just log it and move on
			logMsg( "$src [UNLINK ERROR]: [$@]" );	# this is critical enough to always log
		} else {
			logMsg( "$src [UNLINK SUCCESS]" );	# this is important enough to always log/track
		}	# end "if ( $@ )..." - test for unlink success
		#} #	end "if ( $dsFilePathStatus =~ /Success/i )..."

		return 'COPY SUCCESS', $dest;

	}	# end "if ( $@ )..." - test for copy success



}	# end copyFile2Repo()

sub zipErrorHandler {

	# custom error handler for Archive::Zip; grab the error string normally passed to Carp::carp and return it
	$zipErrorOutput = shift;
	chomp $zipErrorOutput;	# strip any newlines
	return $zipErrorOutput;

}	# end zipErrorHandler()

sub unzipFiles {

	# unzip files for us love!
	my ( $zipFile, $accountName ) = @_;
	my $extractDir = dirname( $zipFile );	# grab the file's location
	logMsg( "$zipFile [EXTRACT TO -> $extractDir]" );

	# set a custom error handler so that we can log error messages and take other appropriate actions
	Archive::Zip::setErrorHandler( \&zipErrorHandler );

	my $zip = Archive::Zip->new();	# instantiate a new archive object

	# read the zip file and confirm it's solid
	#print "Reading the ZIP file...\n";	# debug
	my $readStatus = $zip->read( $zipFile );

	if ( $readStatus == AZ_OK ) {	# 'AZ_OK' is the constant for return value '0'
		logMsg( "$zipFile [READ SUCCESS]" );	# success
		$zipErrorOutput = undef;	# clear this global var for future use
	} else {
		logMsg( "$zipFile [READ FAILED! ($readStatus)]: $zipErrorOutput" );	# failure
		$zipErrorOutput = undef;	# clear global var to prevent false messages
		return $zipFile, 'UNZIP_READ_FAILED';
	}	# end "if ( $readStatus == AZ_OK )..."

	my @unzippedFiles;	# array to hold the list of file names to return when we're done
	logMsg( "$zipFile [" . $zip->numberOfMembers() . " files/members]" );
	foreach my $memberName ( $zip->memberNames() ) {

		#print "\'$zipFile\' -> $memberName\n";	# debug
		my $memberName2Check = $zip->memberNamed( $memberName );
		my $memberIsEncrypted = $memberName2Check->isEncrypted();
		# if encrypted, call unzipWithPassword() and attempt to extract the members if we successfully look up the data source's ZIP password
		if ( $memberIsEncrypted ) {
			logMsg( "unzipWithPassword( $zipFile, $extractDir, $accountName )" );
			my $extractStatus = unzipWithPassword( $zipFile, $extractDir, $accountName );
			# note that since we're inside a 'foreach' loop, success and failure breaks the loop in the relevant 'return' statement below
			if ( $extractStatus eq 'UNZIP_SUCCESS' ) {
				foreach my $memberName ( $zip->memberNames() ) {	 # assign the names to a list to be returned
					my $extractedName = $extractDir . '/' . $memberName;	# remember, we grabbed the zip file's location earlier?
					push @unzippedFiles, $extractedName;	# push the file name into the returned array
				}	# end "foreach my $memberName ( $zip->memberNames() )..." <- after call to unzipWithPassword
				return \@unzippedFiles, $extractStatus; # 'UNZIP_SUCCESS'
			} else {
				return $zipFile, $extractStatus;
			}	# end "if ( $extractStatus eq 'UNZIP_SUCCESS' )..."
		}	# end "if ( $memberIsEncrypted )..."


		# explicitly name the extracted file to prevent files being extracted into bloodhound's home directory; that could get messy!
		my $extractedName = $extractDir . '/' . $memberName;	# remember, we grabbed the zip file's location earlier?
		my $extractStatus = $zip->extractMember( $memberName, $extractedName );
	
		if ( $extractStatus == AZ_OK ) {	# 'AZ_OK' is the constant for return value '0'
			logMsg( "$zipFile: $memberName -> $extractedName [EXTRACT SUCCESS]" );	# success
			push @unzippedFiles, $extractedName;	# push the file name into the returned array
			$zipErrorOutput = undef;	# clear global var to prevent false messages
		} else {	# something failed; assume the worst and return (i.e. do _not_ attempt to extract other members)
			logMsg( "$zipFile: $memberName -> $extractedName [EXTRACT FAILED!]: $extractStatus ($zipErrorOutput)" );	# failure
			return $zipFile, uc( $zipErrorOutput );	# capitalize error output for EMPHASIS
		}	# end "if ( $extractStatus == AZ_OK )..."

	}	# end "foreach my $memberName..."

	return \@unzippedFiles, 'UNZIP_SUCCESS';	# give 'em sumthin' to work on outside...

}	# end unzipFiles()

sub unzipWithPassword {

	# look up the data source's ZIP password and unpack the encrypted/password-protected ZIP file
	# NOTE: we may not always successfully look up a password if that data source profile isn't properly configured; handle accordingly
	my ( $zipFile, $extractDir, $accountName ) = @_;
	my $passwordResult = getDSZipPassword( $dbh, $accountName );
	return 'ZIP_PASSWORD_LOOKUP_ERROR' if $passwordResult eq 'QUERY_ERROR';
	my $zipPassword;
	foreach my $row ( @$passwordResult ) {  # should only be one result returned
		( $zipPassword ) = @$row;
		# jump back, jack!  if the password is empty or undefined
		return 'ZIP_PASSWORD_NOT_DEFINED' if $zipPassword eq "" or ! defined( $zipPassword );
	}	# end "foreach my $row ( @$passwordResult )..."

	# make an external call to the command-line version of 7-Zip to extract these members
	# TECH: the version of WinZip (9.0) we have contains an outdated CLI version that balks at some compression types
	# Archive::Zip doesn't support encrypted members but we'll continue to use it in unzipFiles() as shelling out to external commands is expensive

	#my $zipBin = 'C:/Progra~2/7-Zip/7z.exe';       # C:\Progra~2 == C:\Program Files(x86)
	my $zipBin = '/usr/bin/7z';     # this is Cygwin's instance of 7-Zip
	# extract the member files using the supplied password; file overwrites allowed, explicit extract dir provided as well
	my $zipArgs = "e $zipFile -p$zipPassword -o$extractDir -y";

	#print "CMD: $zipBin $zipArgs\n";       # debug
	my @sevenZipOutput = qx( $zipBin $zipArgs );    # execute!
	if ( $? ) {     # check for non-zero exit status
		#print "ERROR: ", $? >> 8 . "\n";       # bit-shifted error status; debug
		foreach my $line ( @sevenZipOutput ) {
			# strip the pointless "I'm 7-Zip!" header and other junk from the output; concentrate solely on the error message for logging
			chomp $line;
			$line =~ s/\r//;
			next if $line =~ /^7-Zip/;
			next if $line =~ /^$/;
			#print $line . ' ERROR CODE: ', $? >> 8 . "\n"; # bit-shifted error status
			logMsg( "7-Zip: " . $line );	# status message
		}	# end "foreach my $line ( @sevenZipOutput )..."
		return 'ZIP_WITH_PASSWORD_FAILED_UNZIP';
	}	# end "if { $? }..."

	return 'UNZIP_SUCCESS'; # success if we get to this point

}     # end unzipWithPassword()

sub unix2dos {

	# call the unix2dos system command to convert UNIX text files to DOS text files
	# originally written for a Cygwin environment 9/9/2008 ryanfrantz
	# NOTE: the unix2dos command works on the file 'in place'; we may want to account for potential errors and prevent buggering inbound files

	my $file2Convert = shift;	# expect the filename (including full path) to convert as an argument
	# disable STDERR from reporting to the console, ttys, or any other media (i.e. system logs) [2>/dev/null]
	#my $unix2dosCmd = "/usr/bin/unix2dos $file2Convert 2>/dev/null";
	my $unix2dosCmd = "/usr/bin/unix2dos \'$file2Convert\' 2>/dev/null";	# protect us from files that slip through with spaces in file names (\'\')

	system( $unix2dosCmd );	# call the command and its arguments
	if ( $? != 0 ) {	# check the return value
		# "$? >> 8" grabs the actual return value of the called command; run 'perldoc perlop' for more info
		#printf "\'$unix2dosCmd\' failed with return value %d\n", $? >> 8;	# debug
		my $result = sprintf( "UNIX2DOS: \'$unix2dosCmd\' -> [FAILED(RETVAL = %d)]", $? >> 8 );
		logMsg( $result );
		return 'UNIX2DOS_FAILED', $file2Convert;
	} else {
		logMsg( "UNIX2DOS: $file2Convert [SUCCESS]" );
	}	# end "if ( $? != 0 )..."

	return 'UNIX2DOS_SUCCESS', $file2Convert;

}	# end unix2dos()

sub massageFiles {

	# perform file operations based on file extension
	# expect a file name (minus $baseDir) and a file disposition; execute default behavior otherwise
	my ( $accountName, $fileDisposition, $fileName ) = @_;
	if ( !$fileDisposition and !$fileName ) {	# looks like a default call
		my $fileDisposition = 'IN';	# default
		# iterate over the %account2Files hash using $fileDisposition as the key to find files to bark about; *woof*
		foreach my $accountName ( sort keys %{ $account2Files{ $fileDisposition } } ) {

			logMsg( "MASSAGE FILES -> [$accountName]" );
			foreach my $fileRecord ( sort @{ $account2Files{ $fileDisposition }{ $accountName } } ) {

				my ( $fileName, $fileSize, $modTime ) = split /;/, $fileRecord;	# info delimited by semi-colons
				massageFiles( $accountName, $fileDisposition, $fileName );	# make a recursive call to massageFiles to handle the files
			} # end "foreach my $fileRecord..."

		} # end "foreach my $accountName..." for file details

	} else {	# we've got the input we need; proceed

		# prefix $baseDir as we need the full path name for processing (we've previously stripped it out for display purposes)
		my $fullFileName = $baseDir . $fileName;

		# is this file encrypted?
		if ( $fullFileName =~ /(\.gpg$|\.pgp$|\.asc$)/i ) {	# be case-insensitive

			logMsg( "massageFiles(): ENCRYPTED -> $fullFileName" );
			my ( $sourceFile, $decryptFileStatus, $decryptedFile ) = decryptFile( $fullFileName );

			if ( $decryptFileStatus eq 'FILE_DECRYPTED' ) {	# the file was successfully decrypted
				my ( $fileSize, $modTime, $changeTime ) = miniStat( $decryptedFile );
				$decryptedFile =~ s/$baseDir//;	# strip the base dir out
				logMsg( "NEW (DECRYPTED): $decryptedFile | $fileSize bytes | mtime: $modTime" );
				# unlink the original encrypted file
				eval { unlink $fullFileName or die "$!" };
				if ( $@ ) {	# unlink failed; just log it and move on
					logMsg( "massageFiles(): $fullFileName [UNLINK ERROR]: [$@]" );
				} else {
					logMsg( "massageFiles(): $fullFileName [UNLINK SUCCESS]" );
				}	# end "if ( $@ )..." - test for unlink success
				# be recursive and look for additional files that need be be massaged
				massageFiles( $accountName, $fileDisposition, $decryptedFile );
			} else {	# the decryption failed; log it
				my $fileDisposition = 'FAILED2PROCESS';	# failed to process
				my ( $fileSize, $modTime, $changeTime ) = miniStat( $fullFileName );
				logMsg( "DECRYPT FAILURE: $fileName -> [$decryptFileStatus]" );
				push @{ $account2Files{ $fileDisposition }{ $accountName } }, "$fileName -> [$decryptFileStatus]" . ';' . $fileSize . ';' . $modTime;
			}	# end "if $decryptFileStatus eq 'FILE_DECRYPTED'...";

		# is this a ZIP file?
		} elsif ( $fullFileName =~ /(\.zip$)/i ) {	# be case-insensitive
			#logMsg( "massageFiles(): ZIPPED -> $fullFileName" );	# debug
			# send the ZIP file name and account name to unzipFiles(); we'll need the account name for ZIP password lookups
			my ( $unzippedFileList, $unzippedFileStatus ) = unzipFiles( $fullFileName, $accountName );

			if ( $unzippedFileStatus eq 'UNZIP_SUCCESS' ) {

				# then $unzippedFileList is an arrayref...
				foreach my $unzippedFile ( @$unzippedFileList ) {
					my ( $fileSize, $modTime, $changeTime ) = miniStat( $unzippedFile );
					$unzippedFile =~ s/$baseDir//;	# strip the base dir out; sanitize it
					logMsg( "NEW (EXTRACTED): $unzippedFile | $fileSize bytes | mtime: $modTime" );
					# be recursive and look for additional files that need be be massaged
					massageFiles( $accountName, $fileDisposition, $unzippedFile );
				}	# end "foreach my $unzippedFile..."

				# send the member file name to homogenize() to clean it up in case it contains non-standard characters or those that can be shell-interpreted down the line
				my ( $cleanStatus, $cleanedFilename, $filename2Clean ) = homogenize( $fullFileName );	# we need the full path to the file
				if ( $cleanStatus eq 'SUCCESS' ) {
					logMsg( "massageFiles(): HOMOGENIZE [SUCCESS]: $filename2Clean -> $cleanedFilename" );
					# strip $baseDir from $cleanedFilename to match the convention we use for logging
				} else {
					logMsg( "massageFiles(): HOMOGENIZE [FAILED]: $filename2Clean -> $cleanStatus" );
				}	# end "if $cleanStatus eq 'HOMOGENIZE_SUCCESS'..."

				# unlink the original ZIP/archive file
				eval { unlink $fullFileName or die "$!" };
				if ( $@ ) {	# unlink failed; just log it and move on
					logMsg( "massageFiles(): $fullFileName [UNLINK ERROR]: [$@]" );
				} else {
					logMsg( "massageFiles(): $fullFileName [UNLINK SUCCESS]" );
				}	# end "if ( $@ )..." - test for unlink success

			} else {	# unzipFiles() failed for some reason; log it

				my $fileDisposition = 'FAILED2PROCESS';	# failed to process
				my ( $fileSize, $modTime, $changeTime ) = miniStat( $fullFileName );
				# $unzippedFileList is a simple scalar; log the error and index the unzipped filename (no need to call copFile2Repo()...)
				logMsg( "EXTRACT FAILURE: $fileName [$unzippedFileStatus]" );
				push @{ $account2Files{ $fileDisposition }{ $accountName } }, "$fileName -> [$unzippedFileStatus]" . ';' . $fileSize . ';' . $modTime;

			}	# end "if ( $unzippedFileStatus eq 'UNZIP_SUCCESS'..."

		# is this a text file?
		} elsif ( $fullFileName =~ /(\.txt$)/i ) {	# be case-insensitive
			#logMsg( "massageFiles(): TXT -> $fullFileName" );	# debug

			my ( $unix2dosStatus, $isHopefullyDosFile ) = unix2dos( $fullFileName );
			if ( $unix2dosStatus =~ /SUCCESS/ ) {	# we've had a successful unix2dos conversion!
				#logMsg( "UNIX2DOS: $isHopefullyDosFile [SUCCESS]" );	# dupe message from unix2dos; left here for posterity/debugging
				# DO NOT send this back to massageFiles() or we'll end up with an endless loop!!!! we'll take care of this file in this block
				my $fileDisposition = 'MASSAGED';	# successfully massaged
				my ( $fileSize, $modTime, $changeTime ) = miniStat( $fullFileName );
				push @{ $account2Files{ $fileDisposition }{ $accountName } }, $fileName . ';' . $fileSize . ';' . $modTime;
			} else {	# the conversion failed; index it and log the problem
				logMsg( "UNIX2DOS: $isHopefullyDosFile [FAILED TO CONVERT]" );
				my $fileDisposition = 'FAILED2PROCESS';	# failed to process
				my ( $fileSize, $modTime, $changeTime ) = miniStat( $fullFileName );
				push @{ $account2Files{ $fileDisposition }{ $accountName } }, "$fileName -> [$unix2dosStatus]" . ';' . $fileSize . ';' . $modTime;
			}	# end "if ( $unix2dosStatus =~ /SUCCESS/ )..."

		} else {	# just pass the file information on as MASSAGED for the next stage
				my $fileDisposition = 'MASSAGED';	# successfully massaged
				my ( $fileSize, $modTime, $changeTime ) = miniStat( $fullFileName );
				push @{ $account2Files{ $fileDisposition }{ $accountName } }, $fileName . ';' . $fileSize . ';' . $modTime;
		}	# end "if ( $fullFileName =~ /(\.gpg$|\.pgp$|\.asc$)/i; elsif /(\.zip$)/i; elsif /(\.txt$)/i..."

	}	# end "if ( $fileName = '' and $fileDisposition = '' )..."

}	# end massageFiles()

sub xferAll2Repo {

	logMsg( "DEBUG: [getDSFilePath filesMovedFlag = '0']" ) if $debug;
	my $pathResults = getDSFilePath( $dbh, $filesMovedFlag, $userID );
	logMsg( "getDSFilePath RETURNED NO INSTRUCTIONS" ) if @$pathResults == '0';
	return if @$pathResults == '0';
	foreach my $srcDestTuple ( @$pathResults ) {
		my ( $src, $dest ) = @$srcDestTuple;
		logMsg( "DEBUG: copyFile2Repo( $src, $dest )" ) if $debug;
		my ( $copyStatus ) = copyFile2Repo( $src, $dest );
		if ( $copyStatus =~ 'ERROR' ) {
			logMsg( "DEBUG: xferAll2Repo() -> copyFile2Repo(): FAILED" ) if $debug;
			return;	# failure code/reason?
		} else {
			logMsg( "DEBUG: xferAll2Repo() -> copyFile2Repo(): $src -> $dest [$copyStatus]" ) if $debug;
		}	# end "if ( $copyStatus =~ 'ERROR' )..."

	}

	# update the log to the next phase; we won't get here if even a single file failed to get copied properly
	$filesMovedFlag = '1';
	$pathResults = getDSFilePath( $dbh, $filesMovedFlag, $userID );
	logMsg( "DEBUG: [getDSFilePath filesMovedFlag = '1']" ) if $debug;

}	# end xferAll2Repo()


#
# start
#

openlog( $identity, $syslogOptions, $facility );	# open syslog
logMsg( ">>> STARTING RUN" );

parseEmailCfg();

# git me one o' them thar dittybase handles!
$dbh = getDBConnection( $sqlHost, $database, $sqlUsername, $sqlPassword );

logMsg( "Scanning \'$baseDir\'..." ) if $debug;
findFiles( $baseDir );

massageFiles();
xferAll2Repo();

#saveTime();	# save the time for the next run so that we only catch the latest files

my $endTime = time;
my $runTime = $endTime - $startTime;
logMsg( "*** RUN COMPLETE -> Running time: $runTime seconds" );

closelog();	# close syslog

# close our DB connection
$dbh->disconnect();
