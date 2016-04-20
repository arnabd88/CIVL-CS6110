#!/usr/bin/perl
use File::Path qw(make_path);

$input_file = $ARGV[0];
$out_folder = $ARGV[1];
open(INPUT, "<", $input_file) || die "Could not open $input_file";
my $outFH;
my $currentName="";
my $last=3;
my $id=0;
my $tmpDAT="scale.dat.tmp";
my $dat="scale.dat";

#print "$out_folder\n";

open(my $allFH, '>', $tmpDAT) or die "Can't write to file: $!";

print $allFH "Name\t3\t4\t5\t6\t7\t8\t9\t10\t11\t12\t13\t14\t15";

unless (-d $out_folder) {
    mkdir $out_folder;
}

while ($line=<INPUT>) {
  my($name,$size,$time);

  chomp($line);
  next unless ($line =~/^>>>>>>>>\s/);

  #print $line . "\n";
  ($name) = ($line =~/^>>>>>>>>\s(.*)\s<<<<<<<<$/);

  die "no name" unless defined($name);
  $name =~ tr/ //ds;
  if($currentName ne $name){
    $currentName=$name;
    if(defined($outFH)){
      close $outFH;
    }
    open($outFH, '>', "$out_folder/$name.dat") or die "Can't write to file: $!";
    $id++;
    if(($id != 1) and ($last <= 15)){
      for(my $j = $last; $j <= 15; $j++){
	print $allFH "\t-";
      }
    }
    #print "name = $name\n";
    print $allFH "\n$name";
    $last=3;
  }
  
  while ($line=<INPUT>) {
    chomp($line);
    if ($line =~ /time\s\(s\).*:/) {
      #print $line . "\n";
      ($time)=($line =~ /time.*:\s*(\S+)\s*$/);
      last;
    }
  }
  
  while ($line=<INPUT>) {
    chomp($line);
    if ($line =~ /max\sprocess\scount/) {
        #print $line . "\n";
      ($size)=($line =~ /max\sprocess\scount.*:\s*(\d+)\s*$/);
      last;
    }
  }
  
  die "no size" unless defined($size);
  die "no time" unless defined($time);

  # $time=round($time); don't round the time
  $time=1 if $time==0;
  
  next unless ($size >= $last);
  
  if($size>$last){
    #print "size=$size but last=$last\n";
    for (my $i=$last; $i < $size; $i++) {
      print $allFH "\t-";
    }
  }

  print $allFH "\t$time";
  print $outFH "$size\t$time\n";
  $last=$size+1;
  
  # for debugging:

  #print "size = $size\t";
  #print "time = $time\n";
  #print "  $type & $name$cite & $result & $loc & $states & $steps & $time & $mem & $valid & $prove & $scale \\\\","\n";
}
if(($id != 1) and ($last <= 15)){
  for(my $j = $last; $j <= 15; $j++){
    print $allFH "\t-";
  }
}
close $allFH;
open(my $newFH, '>', $dat) or die "Can't write to file: $!";
open(DATA, '<', $tmpDAT) or die "Can't open file: $!";
my $count=0;
my @lines;
my $width;


while ($line=<DATA>) {
  chomp($line);
  @new=split(/\t/, $line);
  $width=@new;
  push @lines, [ @new ]; # split = split( ' ', $_ )
  $count++;
}

for(my $k=0; $k<$width;$k++){
  foreach my $row (@lines) {
    print $newFH $row->[$k] . "\t";
  }
  print $newFH "\n";
}
close $newFH;
close DATA;
unlink $tmpDAT;



