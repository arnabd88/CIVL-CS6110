#!/usr/bin/perl
use Path::Class;
use File::Basename;
use autodie;
use strict;
use warnings;


my $civlDir=".";

my $numArgs = scalar(@ARGV);

if($numArgs > 1){
  warn "At most ONE argument is needed for this script. Additional arguments will be ignored.\n";
}

if($numArgs > 0){
  $civlDir=$ARGV[0];
}else{
  warn "No civl directory is provided, the current directory will be used as the civl directory.\n"
}

my $benchPrefix="edu.udel.cis.vsl.civl.bench.";
my $benchSuffix="Benchmark";
my @benchmarks=($benchPrefix."Adder".$benchSuffix,
		$benchPrefix."Barrier".$benchSuffix,
		$benchPrefix."BlockAdder".$benchSuffix,
		$benchPrefix."DiningPhilosopher".$benchSuffix,
	       $benchPrefix."MessagePassing".$benchSuffix);
my $cmdStart="java -classpath $civlDir/civl.jar:$civlDir/bin ";

foreach my $benchmark (@benchmarks){
  my $result = `$cmdStart $benchmark $civlDir`;
  print $result;
}

