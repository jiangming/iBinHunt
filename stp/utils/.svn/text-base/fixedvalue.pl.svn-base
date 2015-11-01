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
my $cpmodel="cp ".$model." tempmodel.stp"; 

# Reading original request
my $buffer = "";
open(REQUEST, $reqfile); 
binmode(REQUEST); 
my $count=read(REQUEST, $buffer, 4096); 
close(REQUEST); 
my @request=unpack("C*", $buffer); 

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

for ($i=0; $i<$count; $i++) {
    if ($fixedvalue[$i] == 1) { 
	print STDERR "  Testing byte $i ...\n";
	
	my $query = "";	 
	my $hexval = sprintf "0hex%02X", $request[$i]; 
	$query = $query."QUERY (post = 0bin0) OR (INPUT\_$i = $hexval)";
	#print STDERR $cpmodel, "\n";
        system("sed -e 's/ASSERT.*0bin1.*/post : BITVECTOR(1);ASSERT( post =/g' $model > tempmodel.stp");
	open(MODEL, ">>tempmodel.stp");
	print MODEL $query, ";\n";
	close(MODEL);

	print STDERR "  Running stp query ...\n";
	my $ret = system("$stp tempmodel.stp > stpoutput"); 
	if ($ret == 2) {
	    print STDERR "Aborted: STP killed\n";
	    exit(1);
	}

	open(STPOUT, "stpoutput");
	while (<STPOUT>) {
	    if (m/Invalid.*/) {
		# STP returned Invalid, there are other values possible
		$fixedvalue[$i] = 0; 
	    }
	}
    }

    if ($fixedvalue[$i] == 1) {
	printf STDERR "byte %d: TRUE\n", $i;
    } else {
	printf STDERR "byte %d: false\n", $i;
    }

    printf "INPUT_%d : %d\n", $i, $fixedvalue[$i]; 
}

