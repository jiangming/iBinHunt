#!/usr/bin/perl
use warnings;
use strict; 

my $argc = @ARGV; 
if ($argc < 2) {
    printf "Usage: %s stpfile requestfile\n", $0;
    exit 1;
}

my $model=$ARGV[0]; 
my $reqfile=$ARGV[1];

my $stp="/home/zliang/bin/stp";

# Reading original request
my $buffer = "";
open(REQUEST, $reqfile); 
binmode(REQUEST); 
my $count=read(REQUEST, $buffer, 4096); 
close(REQUEST); 
my @request=unpack("C*", $buffer); 


system("sed -e 's/ASSERT.*0bin1.*/post : BITVECTOR(1);ASSERT( post =/g' $model > tempmodel.stp");

my $i; 

my @fixedvalue;
for ($i = 0; $i<$count; $i++) {
    $fixedvalue[$i] = 0; 
}

open(MODEL, $model); 
while(<MODEL>) {
    if (m/INPUT_([0-9]*).*BITVECTOR.*/) {
	$fixedvalue[$1] = 1; 
    }
}
close(MODEL);

open(TMPMODEL, ">>tempmodel.stp");
for ($i=0; $i<$count; $i++) {
    if ($fixedvalue[$i] == 1) {
	my $assert = sprintf "ASSERT(INPUT_%d = 0hex%02X);\n", $i, $request[$i];
	print TMPMODEL $assert;
    }
}
print TMPMODEL "QUERY post=0bin0;\n";
close(TMPMODEL); 

system("$stp tempmodel.stp");

print "It is a valid input if the above query returns 'Invalid.'\n";
print "We can not query whether the post condition is always true, because of uninitialized memories.\n";

