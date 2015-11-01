#!/usr/bin/perl
use warnings; 
use strict; 
use File::Basename;

my $model=$ARGV[0]; 
my $varname=$ARGV[1];
my $varstart=$ARGV[2]; 
my $varend=$ARGV[3];
my $size=$ARGV[4];
my $mode=$ARGV[5]; 

my $argc = @ARGV; 
if ($argc < 6) {
    printf STDERR "Usage: %s stpmodel varname varstart varend size mode\n", $0;
    exit 1;
}

my $stp_path = "stp";
if ($argc == 7) {
    $stp_path = $ARGV[6];
}

my $bindir=dirname($0); 

my $i; 
my $oneword = "01"; 
my $zeroword = "00"; 
my $ffword = "FF"; 
my $feword = "FE"; 
for ($i = 0; $i<$size/8-1; $i++) {
   $oneword = "00".$oneword; 
   $zeroword = "00".$zeroword; 
   $ffword = "FF".$ffword; 
   $feword = "FF".$feword; 
}

my $oneall = $oneword; 
my $zeroall = $zeroword; 
my $ffall = $ffword; 
my $feall = $feword; 
my $variable = "$varname\_$varstart"; 

for ($i = $varstart+1; $i <= $varend; $i++) {
    $variable = "$varname\_$i@".$variable;
    $oneall = $zeroword.$oneall; 
    $zeroall = $zeroword.$zeroall; 
    $ffall = $ffword.$ffall; 
    $feall = $ffword.$feall; 
}
$oneall = "0hex".$oneall;
$zeroall = "0hex".$zeroall;
$ffall = "0hex".$ffall;
$feall = "0hex".$feall;

print STDERR "Variable is: ", $variable, "\n";

my %left_bounds;
my %right_bounds; 

sub base_formula {
    system("cp $model temp1.stp");
    system("cp temp1.stp temp2.stp"); 
    system("sed -i -e 's/$varname/F2\_$varname/g' temp2.stp");
    my $varsize = ($varend-$varstart+1)*$size; 
    open (TEMP1, ">>temp1.stp"); 
    printf TEMP1 "temp_val : BITVECTOR(%d);\n", $varsize;
    for ($i = $varstart; $i <= $varend; $i++) {
	printf TEMP1 "F2_%s_%d : BITVECTOR(%d);\n", $varname, $i, $size;
    }
    close(TEMP1);
    system("$bindir/prepareformula.pl temp1.stp temp2.stp > tmptemp2.stp"); 
    system("mv tmptemp2.stp temp2.stp"); 
}

sub new_formula {
    my $type = $_[0]; 

    my $operator;
    if ($type eq "left") {
	$operator = "BVSUB"; 
    } else {
	$operator = "BVPLUS"; 
    }    

    my $varsize = ($varend-$varstart+1)*$size; 
    open(TEMPCONN, ">tempconn.stp"); 
    printf TEMPCONN "ASSERT( temp_val = $operator(%d, %s, %s));\n", 
    $varsize, $variable, $oneall; 
    for ($i = $varstart; $i <= $varend; $i++) {
	printf TEMPCONN "ASSERT(F2_%s_%d = temp_val[%d:%d]);\n", $varname, $i, 
	($i-$varstart+1)*$size-1, ($i-$varstart)*$size; 
    }
    close(TEMPCONN);  

    system("cat temp1.stp tempconn.stp temp2.stp > tempmodel.stp");
}

sub get_bound {
    my $bound;
    my $i;

    my $type = $_[0]; 
    my $mode = $_[1]; 
    my $curbound = $_[2]; 
    
    my $operator;
    my $compop; 
    if ($type eq "left") {
	$compop = "BVLT";
    } else {
	$compop = "BVGT";
    }
 
    my $query = "QUERY (F1 = 0bin0) OR (F2 = 0bin1)"; 

    my %bounds; 
    if ($type eq "left") {
	%bounds = %left_bounds;
    } else {
	%bounds = %right_bounds; 
    }
    
    if ($mode eq "all") {
	for (keys %bounds) {
	    $query = $query." OR ($variable = $_)"; 
	}
    } else {
        if ($curbound ne "") {	
	    $query = $query." OR (NOT $compop($variable, $curbound))";
        }
    }
    print STDERR $query, "\n";
    open(MODEL, ">>tempmodel.stp");
    print MODEL $query, ";\nCOUNTEREXAMPLE;";
    close(MODEL);

    my $ret = system("$stp_path tempmodel.stp >stp.out 2>&1"); 
    if ($ret == 2) {
	print STDERR "Aborted: STP killed\n";
	exit(1);
    } else {
        if ($ret == 65280) {
	    #tested var not in formula
	    if ($type eq "left") {
                return $zeroall;
	    } else {
		return $ffall;
	    }
        }
    }
    open(OUTPUT, "<stp.out");
    my $resultfile="result";
    open(RESULT, ">".$resultfile); 
    my @result; 
    my $isvalid = 0; 
    while (<OUTPUT>) {
	if (m/.*Valid.*/) {
	    $isvalid = 1;
	}
	if (m/.* +$varname\_([^ ]*) *= *0hex([^ ]*).*/) {
	    if ($1 >= $varstart && $1 <= $varend) {
		#print "$1: $2\n";
		$result[$1-$varstart] = hex($2); 
	    }
	}
    } 
    close(RESULT); 
    close(OUTPUT);

    if ($isvalid == 1) {
	$bound = ""; 
    } else {
	$bound = "";
	for ($i = $varstart; $i <= $varend; $i++) {
	    my $format = sprintf "%%0%dX", $size/4; 
	    my $temp = sprintf $format, $result[$i-$varstart]; 
	    if ($i == $varstart) {
		$bound = $temp; 
	    }
	    else {
		$bound = $temp.$bound; 
	    }
	}
	$bound = "0hex".$bound;
    }

    return $bound; 
}


my $lastval; 
my $val = "nonempty";
my $currentbound = "";

base_formula;

my $directtest = 1; 
$currentbound = $oneall; # try the left most first;
until ($val eq "") {
    new_formula "left";
    $val = get_bound("left", $mode, $currentbound); 
    if ($val ne "") {
	if ($mode ne "all") {
	    $currentbound = $val; 
	} else {
	    $left_bounds{$val} = 1; 
	}
	print STDERR "Left bound: ", $val, "\n";
	$lastval = $val; 
	if ($mode eq "all") {
	   print "$val-L\n";
	}
    }
    
    if ($directtest == 1) {
	if ($val eq $zeroall) {
	    $val = ""; # terminate
	} else {
	    $directtest = 0;
	    $val = "nonempty"; # continue
	    $currentbound = "";
	}
    }
};

print STDERR "Done with left bounds\n";

if ($mode ne "all") {
    print "Leftmost bound: $lastval\n";
}

$val = "nonempty";
$currentbound = "";

$directtest = 1; 
$currentbound = $feall; # try the left most first;
until ($val eq "") {
    new_formula "right";
    $val = get_bound("right", $mode, $currentbound); 
    if ($val ne "") {
	if ($mode ne "all") {
	    $currentbound = $val; 
	} else {
	    $right_bounds{$val} = 1; 
	}
	print STDERR "Right bound: ", $val, "\n";
	$lastval = $val; 
	if ($mode eq "all") {
	   print "$val-R\n";
	}
    }
    if ($directtest == 1) {
	if ($val eq $ffall) {
	    $val = ""; # terminate
	} else {
	    $directtest = 0;
	    $val = "nonempty"; # continue
	    $currentbound = "";
	}
    }
};

print STDERR "Done with right bounds\n";

if ($mode ne "all") {
    print "Rightmost bound: $lastval\n";
}


