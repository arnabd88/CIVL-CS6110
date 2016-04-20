#!/usr/bin/perl
use Path::Class;
use File::Basename;
use autodie;
use strict;
use warnings;

#my $civlDir="/Users/zmanchun/civl";
my $civlDir=".";
my $numArgs = scalar(@ARGV);
my $outfile="";
my $out;
my $hasCivlDir=0;

if($numArgs > 2){
  warn "At most ONE argument is needed for this script. Additional arguments will be ignored.\n";
}

if($numArgs > 0){
  for(my $i=0; $i < 2; $i++){
    # print "$ARGV[$i]\n";
    my $arg=$ARGV[$i];
    
    if($arg =~ /^\-o(.*)$/){
      #$outfile=($arg =~ /\-o(\S+)$/);
      $outfile=$1;
      # print "outfile is $outfile\n";
      $out = *STDOUT unless open($out , '>', $outfile );
      # print "out is $out\n";
    }else{
      $civlDir=$arg;
      $hasCivlDir = 1;
    }
  }
}
if($hasCivlDir==0){
  warn "No civl directory is provided, the current directory will be used as the civl directory.\n"
}
if(!defined($out)){
  # print "use stdout.\n";
  $out=*STDOUT;
}
# print "CIVL directory: $civlDir\n";
# print "output: $out\n";

my $benchPrefix="edu.udel.cis.vsl.civl.bench.scale.";
my $benchSuffix="BenchmarkScale";
my @benchmarks=($benchPrefix."Adder".$benchSuffix,
		$benchPrefix."Barrier".$benchSuffix,
		$benchPrefix."BlockAdder".$benchSuffix,
		$benchPrefix."DiningPhilosopher".$benchSuffix,
	       $benchPrefix."MessagePassing".$benchSuffix);
my $cmdStart="java -classpath $civlDir/civl.jar:$civlDir/bin ";

foreach my $benchmark (@benchmarks){
  my $result = `$cmdStart $benchmark $civlDir`;
  print $out $result;
}

print "Scale benchmarks finished.\n"



