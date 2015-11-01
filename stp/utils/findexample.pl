#!/usr/bin/perl
# Takes two arguments, stp file, base query

my $argc = @ARGV;
if ($argc < 3) {
    printf STDERR "Usage: %s stpformula counter requestfile\n", $0;
    exit 1;
}



$model=$ARGV[0]; 
$counter=$ARGV[1];
$requestfile=$ARGV[2];
if ($counter == 0) {
    $basequery="basequery";
} else {
    $basequery=$counter."/nextquery";
}

$query="";
open(F, $basequery); 
while (<F>) {
    $query = $query.$_;
}
close(F);

$stp="$HOME/research/vine/stp/stp";
$cpmodel="cp ".$model." model.stp"; 

while (1) {
    $counter = $counter + 1;
    print "Creating test directory ", $counter, "\n";
    mkdir("$counter");
    
    $newquery = $query;

    print "Building stp query ...\n";
    print $cpmodel, "\n";
    system($cpmodel);
    open(MODEL, ">>model.stp");
    print MODEL $query, ";\nCOUNTEREXAMPLE;\n";
    close(MODEL);

    # Reading original request
    $buffer = "";
    open(REQUEST, "<$requestfile"); 
    binmode(REQUEST); 
    read(REQUEST, $buffer, 1024); 
    close(REQUEST); 
    @request=unpack("C*", $buffer); 
    
    print "Running stp query ...\n";
    system("$stp model.stp >/tmp/stpout 2>&1"); 
    system("ls -l /tmp/stpout");
    system("cp /tmp/stpout ".$counter); 
    open(OUTPUT, "</tmp/stpout");
    $resultfile=$counter."/result";
    open(RESULT, ">".$resultfile); 
    $first = 1; 
    while (<OUTPUT>) {
	if (m/.*INPUT_(.*)  = 0hex(.*) .*/) {
	    $request[$1]=hex($2); 
	    if ($first == 1) {
		$newquery = $newquery." OR ( ";
		$first = 0; 
	    } else {
		$newquery = $newquery." AND ";
	    }
	    $newquery = $newquery." INPUT_".$1."=0hex".$2;
	    printf RESULT "%03s 0x%s\n", $1, $2; 
	}
    } 
    close(RESULT); 
    close(OUTPUT);
    $cmd="sort ".$resultfile." -o ".$resultfile.".sort";
    system($cmd); 
    if ($first == 0 ) {
	$newquery = $newquery.")\n";
    }
# Construct next query
    
    print $newquery, "\n";

    print "Writing next query ...\n";
    $queryfile=">".$counter."/nextquery";
    open(LASTQUERY, $queryfile); 
    print LASTQUERY $newquery, "\n";
    close(LASTQUERY);
    $query=$newquery;
    
# CONVERT to output and check whether it is accepted by servers
    print "Writing resulting request ...\n";
    open(REQUEST, ">".$counter."/request"); 
    binmode(REQUEST);
    $buffer = pack("C*", @request); 
    syswrite(REQUEST, $buffer);
    close(REQUEST);

}
