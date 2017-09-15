#!/bin/perl

printf ("\n");
printf ("=============================\n");
printf ("Generating Regression Summary\n");
printf ("=============================\n\n");

my @logfiles = `find logs -name \"\*.log\"`;
my $logcount = $#logfiles+1;
my $pass_total, $fail_total, $other_total, $test_total = 0;

foreach my $logfile (@logfiles){
  my $pass = `grep PASS $logfile`; 
  my $fail = `grep FAIL $logfile`; 
  if($pass){
    printf ("  PASS    ->   %s", $logfile);
    ++$pass_total;
  } elsif ($fail){
    printf ("  FAIL    ->   %s", $logfile);
    ++$fail_total;
  } else {
    printf ("  UNKNOWN ->   %s", $logfile);
    ++$other_total;
  }
  ++$test_total;
}

my $pass_percent  = ($pass_total/$test_total)*100;
my $fail_percent  = ($fail_total/$test_total)*100;
my $other_percent = ($other_total/$test_total)*100;

printf ("\n");
printf ("===============================================================================\n");
printf ("REGRESSION SUMMARY => PASS: %d[%d\%], FAIL: %d[%d\%], UNKNOWN: %d[%d\%], TOTAL: %d\n", $pass_total, $pass_percent, $fail_total, $fail_percent, $other_total, $other_percent, $test_total);
printf ("===============================================================================\n\n");
