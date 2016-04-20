#!/usr/bin/perl
use File::Temp;

sub substitute {
    my($oldstring) = $_[0];
    my($newstring) = $_[1];
    my($filename) = $_[2];
    my($line);
    my($found) = 0;

    my($tmpfile) = "PERLSUBTMPFILE";
    open(OLDFILE, "<$filename") || die "Could not open $filename";
    
    while (!$found && defined($line=<OLDFILE>)) {
	if ($line =~ /$oldstring/) {
	    print "String found in $filename: $line";
	    print "Substituting within this file\n\n";
	    $found = 1;
	}
    }
    close(OLDFILE) || die "Could not close $filename";

    if ($found) {
	open(OLDFILE, "<$filename") || die "Could not open $filename";
	open(NEWFILE, ">$tmpfile") || die "Could not open $tmpfile";
	while (defined($line=<OLDFILE>)) {
	    $line =~ s/$oldstring/$newstring/g;
	    print NEWFILE $line;
	}
	close(OLDFILE) || die "Could not close $filename";
	close(NEWFILE) || die "Could not close $newfile";
	unlink($filename) || die "Could not delete $filename";
	rename $tmpfile, $filename || die "Could not rename $tmpfile to $filename";
    }
}

$numargs = $#ARGV + 1;
# print "num args is $numargs\n";
# print "arg0: $ARGV[0]\t arg1: $ARGV[1]\n";
die "At least 3 arguments required: old string, new string, one or more file names"
    unless $numargs >= 3;
foreach $file (@ARGV[2..$#ARGV]) {
    printf("Examining file $file...\n");
    &substitute($ARGV[0], $ARGV[1], $file);
}
1;
