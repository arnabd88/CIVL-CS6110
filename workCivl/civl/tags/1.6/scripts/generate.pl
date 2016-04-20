#!/usr/bin/perl

use strict;
use warnings;
use Path::Class;
use autodie;
use File::Basename;

my $numArgs = scalar(@ARGV);

my $folder = dir(".");

my $outName = "Makefile";

if($numArgs > 1){
  warn "At most ONE argument is needed for this program. Additional arguments will be ignored.\n";
}

if($numArgs > 0){
  if($ARGV[0] eq "help"){
    printHelp();
    exit;
  }else{
    if((not -d $ARGV[0]) and (not -e $ARGV[0])){
      print "The file or directory $ARGV[0] doesn't exist!\n";
      print "Please use a valid file or directory.\n";
      exit;
    }else{
      $folder = dir("$ARGV[0]");
    }
    if($numArgs > 1){
      $outName = $ARGV[1];
    }
  }
}

open(my $fileHandle, '>', "$outName") or die "Can't write to file: $!";
print $fileHandle "CIVL=civl\n";
print $fileHandle "VERIFY=\$(CIVL) verify -enablePrintf=false\n";
traverse($folder, $fileHandle);
close $fileHandle;
print "Makefile generated for $folder successfully\n";


sub printHelp{
print "======= HELP =======\n";
print "This script is to generate a Makefile for c/cvl/cu files in a given folder.\n";
print "Usages:\n";
print "perl generate.pl: generate Makefile for all C/CIVL-C program in the CURRENT folder\n";
print "perl generate.pl dirname: generate Makefile for all C/CIVL-C program in the given folder\n";
print "perl generate.pl dirname filename: generate Makefile for all C/CIVL-C program in the given folder and save it as the given filename\n";
print "perl generate.pl help: show this message\n";
}

sub traverse{
  my ($dir) = $_[0];
  my ($out) = $_[1];
  my (@files);

  print $out "all: ";
  if(not -d $dir){
    return;
  }
  print "working in $dir\n";
  return if not -d $dir;
  while(my $file = $dir->next){
    next if $file eq "$dir"
      or $file eq "$dir" . '/..'
      or $file->basename eq "CIVLREP";
    #print $file->stringify . "\n";
    my $target;
    unless($file->is_dir()){
      if ($file =~ /\.(c|cvl|cu)/) {
	my $target = basename("$file",  "");

	# print "file is " . $file->stringify . "\n";
	push(@files, $target);
	($target = $target) =~ s/\.[^.]+$//;
	# print "target is $target \n";
	print $out $target . " ";
      }
    }
  }
  print $out "\n";
  foreach (@files) {
    my $target;
    my $file = $_;

    ($target = $file) =~ s/\.[^.]+$//;
    print $out "\n" . $target . ": $file\n";
    print $out "\t" . "\$(VERIFY) $file\n";
  }
}
