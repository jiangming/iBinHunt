#!/usr/bin/perl

$argc = @ARGV; 
$formula1 = $ARGV[0];
$formula2 = $ARGV[1]; 

if ($argc < 2) {
    printf "Usage: %s formula1 formula2\n", $0; 
    exit 1; 
}
# Create a hash table to hold all variable declarations in formula one

print "F1 : BITVECTOR(1);\n";
print "F2 : BITVECTOR(1);\n";


open(F1, "$formula1"); 
while (<F1>) {
    if (m/ASSERT.*0bin1.*=.*/) {
	print "ASSERT(F1 =\n"; 
    } else {
	if (m/([^ ]*)( *):( *)BITVECTOR.*/) {
	    if (!$vardecl1{$1}) {
		$vardecl1{$1} = 1; 
		print; 
	    }
	} else {
	    print ; 
	}
    }
}
close(F1);

open(F2, "$formula2"); 
while (<F2>) {
    if (m/([^ ]*)( *):(.*)BITVECTOR(.*)/) {
	my $varname = $1; 
	my $newline = "$2:$3BITVECTOR$4\n";

	# a hack for range search, input vars already been replaced with F2_.
	if ($varname =~ m/F2.*/ || $varname =~ m/INPUT.*/) {
	    $newvar = $varname; 
	} else {
	    $newvar = "F2\_$1"; 
	}
	$newline = $newvar.$newline;
	if (!$vardecl1{$newvar}) {
	    print $newline;
	}
    } else {
	if (m/ASSERT.*0bin1.*=.*/) {
	    print "ASSERT(F2 =\n"; 
	} else {
	    if (m/.*LET *([^ _]*)_[^ ]* *=.*/) {
		$var2{$1} = "F2_".$1; 
	    }
	    $line = $_; 
	    for (keys %var2) {
		$line =~ s/(?<!\w)$_(?=_)/$var2{$_}/g;
	    }
	    print $line; 
	}
    }
}
close(F2); 

