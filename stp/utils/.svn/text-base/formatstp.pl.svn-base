#!/usr/bin/perl
$model=$ARGV[0]; 

open(MODEL, $model);
while (<MODEL>) {
    if (m/(.*)INPUT_([0-9]*)_([0-9]*)(.*)_([0-9]*)(.*)/) {
	print $1, "INPUT_", $3, $6, "\n";
    } else {
	print $_; 
    }
}
close(MODEL); 



