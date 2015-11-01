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
my @constraint; 
for ($i = 0; $i<$count; $i++) {
    $constraint[$i] = 0; 
}

open(MODEL, $model); 
while(<MODEL>) {
    if (m/INPUT_([0-9]*).*BITVECTOR.*/) {
	$constraint[$1] = 1; 
    }
}
close(MODEL);

for ($i=0; $i<$count; $i++) {
    if ($constraint[$i] == 1) { 
	print STDERR "  Testing byte $i ...\n";
	
	my $query = "";	 
	for (my $j = 0; $j<$count; $j++) {
	    if (($j != $i) && ($constraint[$j] == 1)) {
		$query = $query.sprintf("ASSERT(INPUT_%d = 0hex%02x);\n",
					$j, $request[$j]); 
	    }
	}
	$query = $query."QUERY (post = 0bin1) ";
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
	    if (m/Valid.*/) {
		print STDERR "  STP returned Valid.\n";
		$constraint[$i] = 0; 
	    }
	}
    }

    if ($constraint[$i] == 1) {
	printf STDERR "byte %d: TRUE\n", $i;
    } else {
	printf STDERR "byte %d: false\n", $i;
    }

    printf "INPUT_%d : %d\n", $i, $constraint[$i]; 
}

