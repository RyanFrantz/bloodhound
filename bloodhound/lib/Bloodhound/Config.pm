package Bloodhound::Config;

#
#	export some sensitive variables to bloodhound (note that these can still be "seen" in memory)
#

use warnings;
use strict;
use Exporter;
our ( @ISA, @EXPORT, $VERSION );
@ISA = ( "Exporter" );
@EXPORT = qw( $gpgbin $secretkey $passphrase $sqlHost $database $sqlUsername $sqlPassword $debug );
$VERSION = '1.0';

our $gpgbin = '/usr/bin/gpg';	# path to the GPG binary
our $secretkey = '1234abcd';	# the ID of our default secret key
our $passphrase = 'sekrit';	# the passphrase for our default secret key

# SQL Server-related variables we'll need to connect - 5/19/2008 ryanfrantz
our $sqlHost = 'sqlhost.example.com';
our $database = 'MOAR-DATA';
our $sqlUsername = 'bloodhound';
our $sqlPassword = 'sql-sekrit';

our $debug = '0';	# set to a true value to enable extra logging

1;	# end package Bloodhound::Config
