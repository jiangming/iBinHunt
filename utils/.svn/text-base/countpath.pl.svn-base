#!/usr/bin/perl
#  Owned and copyright BitBlaze, 2007. All rights reserved.
#  Do not copy, disclose, or distribute without explicit written
#  permission.

#    This program counts the number of acyclic paths in a dot file
   
#    @author Zhenkai Liang

use warnings;
use strict; 

my $startlabel = "-5"; 
my $endlabel = "-6";

my $argc = @ARGV;
if ($argc < 1) {
    printf STDERR "Usage: %s dotfile\n", $0;
    exit 1;
}

my %edgetable; 
my %nodetable; 

open(DOTFILE, $ARGV[0]); 
while (<DOTFILE>) {
    if (m/([\t ]*)([^ ]*) *-> *([^ ;]*).*/) {
	my $edge = $2."->".$3; 
	$edgetable{$edge} = 0; 
	$nodetable{$2} = 0;
	$nodetable{$3} = 0;
    }
}
close(DOTFILE); 

my %vset;
my %newvset; 

# set the number paths to the start node
$nodetable{$startlabel} = 1; 


$vset{$startlabel} = 1; 

my %visited; 
$visited{$startlabel} = 1; 

while (1) {
    %newvset = ();
    for (keys %edgetable) {
	if (m/(.*)->(.*)/) {
	    if ($vset{$1}) {
		$visited{$1} = 1;
		if (!$visited{$2}) {
		    $newvset{$2} = 1; 
		}
		$nodetable{$2} += $nodetable{$1}; 
	    }
	}
    }
    %vset = %newvset; 
    
    my $hashsize;
    $hashsize = keys %vset; 
    
    if ($hashsize == 0) {
	last; 
    }
}

print $nodetable{$endlabel}, "\n";
