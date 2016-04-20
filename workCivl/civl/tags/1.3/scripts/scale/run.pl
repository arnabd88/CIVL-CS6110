#!/usr/bin/perl

my $civlDir="."; # directory to civl
my $numArgs = scalar(@ARGV);
my $out = "scale.pdf";
my $benchOut = "bench.scale.out";

for(my $i=0; $i < $numArgs; $i++){
  my $arg = $ARGV[$i];

  if($arg =~ /^\-d(.*)$/){
    $civlDir=$1;
  }elsif ($arg =~ /^\-o(.*)$/){
    $out = $1;
    if(!($out =~ /\.pdf$/)){
      warn "$out is not a pdf file name, $out.pdf will be used for output file instead.\n";
      $out="$out.pdf";
    }
  }else{
    warn "Arguments should start with -d or -o, invalid argument $arg would be ignored.\n";
  }
}

my $scriptPrefix="$civlDir/scripts/scale";

print "running scale benchmarks...\n";
my $cmd = `$scriptPrefix/runBenchScale.pl $civlDir -o$benchOut`;
print "scale benchmarks finished, now generating .dat file...\n";
$cmd = `$scriptPrefix/parseScale.pl $benchOut`;
print ".dat file finished, now generating figure...\n";
$cmd = `gnuplot $scriptPrefix/plotScale`;
print "scaling figure is successfully generated in $out\n";

