#!/usr/bin/perl

use strict;
use warnings;
use Data::Dumper;
use File::Copy;
use File::Path;
use FileHandle;

##################################
sub Usage {
  print <<EOF;

Usage: run_regress.pl 
       run_regress.pl dir1 dir2 ...
       run_regress.pl -h ( for help )

Finds all runsim files below the current directory and executes them.
If directories are specified then only those directories will be searched.
Gets the results from vcs.log and creates a summary.log
Cleans up the run directories after getting the results.

EOF
}

##################################

if ( defined(@ARGV) && $ARGV[0] =~ /-h/ ) {
  Usage();
  exit(0);
}

my $outfile = "summary.log";
my $logfile = "vcs.log";
my %result;
my $pwd = `pwd`;
chomp($pwd);
if ( $#ARGV >= 0 ) {
  foreach my $dir ( @ARGV ) {
    if ( -d $dir ) {
      RecurseDir($dir);
    }
  }
}
else {
  RecurseDir(".");
}
GenSummary();
exit(0);

##################################
sub RecurseDir {
  my ($path) = @_;
  #print "path = $path\n";
  my @files = ReadDir($path);
  foreach my $file ( @files ) {
    next if ( $file =~ /^\./ );
    my $full = "$path/$file";
    #print "full = $full\n";
    if ( $file =~ /runsim/ ) {
      RunTest($path,$file);
    }
    elsif ( -d $full ) {
      RecurseDir($full);
    }
  }
}

##################################
sub RunTest {
  my($runDir,$runsim) = @_;
  chdir($runDir);
  $runDir =~ /(\w+)$/;
  my $dir = $1;
  my $cmd = "$runsim > regress.log";
  system($cmd);
  print "Running: $runDir\n";
  my $INFILE = OpenInRef($logfile);
  if ( defined($result{$dir}) ) {
    print "ERROR duplicate test dir name: $dir\n";
  }
  $result{$dir}{status} = "unknown";
  $result{$dir}{seed} = "unknown";
  $result{$dir}{"time"} = "unknown";
  while( my $line = <$INFILE> ) {
    if ( $line =~ /^(PASS|FAIL)/ ) {
      $result{$dir}{status} = $1;
    }
    elsif ( $line =~ /random seed used: (\d+)/ ) {
      $result{$dir}{seed} = $1;
    }
    elsif ( $line =~ /^\$finish at simulation time\s+(\d+)/ ) {
      $result{$dir}{"time"} = $1;
    }
  }
  close($INFILE);
  system("./CLEAN");
  chdir($pwd);
}

##################################
sub GenSummary {
  my $tc = 0;
  my $pc = 0;
  my $fc = 0;
  foreach my $dir ( keys %result ) {
    $tc++;
    if ( $result{$dir}{status} eq "PASS" ) {
      $pc++;
    }
    if ( $result{$dir}{status} eq "FAIL" ) {
      $fc++;
    }
  }
  my $nc = $tc-$pc-$fc;
  
  my $FHOUT = OpenOutRef($outfile);
  print "Creating file: $outfile\n";
  print $FHOUT "Total tests run: $tc\n";
  print $FHOUT "Total pass tests: $pc\n";
  print $FHOUT "Total fail tests: $fc\n";
  print $FHOUT "Total no result tests: $nc\n";
  foreach my $dir ( sort keys %result ) {
    printf $FHOUT ("%-25s  status = %-7s  seed = %-10s  time = %s\n", $dir, $result{$dir}{status}, $result{$dir}{seed}, $result{$dir}{"time"} );
  }
}

##################################
sub OpenInRef {
  my ($file) = @_;
  my $INFILE = FileHandle->new;
  if ( $INFILE->open("< $file") == 0 ) {
    print "Error unable to open in file: $file\n";
    exit(1);
  }
  return $INFILE;
}

##################################
sub OpenOutRef {
  my ($file) = @_;
  my $OUTFILE = FileHandle->new;
  if ( $OUTFILE->open("> $file") == 0 ) {
    print "Error unable to open out file: $file\n";
    exit(1);
  }
  return $OUTFILE;
}

##################################
sub ReadDir {
  my($dir) = @_;
  if ( opendir(DIR, $dir) ) {
    my @file = readdir(DIR);
    chomp(@file);
    closedir(DIR);
    return @file;
  }
  else {
    print "Error: Unable to open directory $dir\n $!";
    exit(1);
  }
}

