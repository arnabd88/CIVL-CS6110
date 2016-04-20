#!/usr/bin/perl
use Path::Class;
use File::Basename;
use autodie;
use strict;
use warnings;
use File::Path qw(make_path);

my $civlDir="."; # directory to civl
my $numArgs = scalar(@ARGV);
my $datOut = ".";
my $benchOut = "bench.scale.out";
my $hasCivlDir=0;
my $datDir;

for(my $i=0; $i < $numArgs; $i++){
  my $arg = $ARGV[$i];

  if($arg =~ /^\-d(.*)$/){
    $civlDir=$1;
    $hasCivlDir=1;
  }elsif ($arg =~ /^\-o(.*)$/){
    $datOut = $1;
    #if(!($datOut =~ /\.pdf$/)){
      #warn "$out is not a pdf file name, $out.pdf will be used for output file instead.\n";
     # $out="$out.pdf";
   # }
  }else{
    warn "Arguments should start with -d or -o, invalid argument $arg would be ignored.\n";
  }
}

if($hasCivlDir == 0){
  warn "no civl directory is provided, current directory will be used as the civl directory.\n";
}

unless (-d $datOut) {
    mkdir $datOut;
}
$benchOut="$datOut/$benchOut";

my $scriptPrefix="$civlDir/scripts/scale";

print "running scale benchmarks...\n";
my $cmd = `$scriptPrefix/runBenchScale.pl $civlDir -o$benchOut`;
print "scale benchmarks finished, now generating .dat file in $datOut...\n";
$cmd = `$scriptPrefix/parseScale.pl $benchOut $datOut`;
print ".dat file finished, now generating figure...\n";

$datDir=dir("$datOut");
while(my $datFile = $datDir->next){
  next unless ($datFile =~ /\.dat$/);
  my $benchmark;

  $datFile = basename($datFile,  "");
  ($benchmark) = ($datFile =~ /(.*)\.dat/);
  print "plotting figure for benchmark $benchmark...\n";
  $cmd = `gnuplot -e "TITLE='$benchmark'" -e "DAT_FILE='$datOut/$datFile'" -e "OUT_FILE='$datOut/$benchmark.pdf'" $scriptPrefix/plotBench.plg`;
}
print "scaling figures is successfully generated in $datOut\n";
