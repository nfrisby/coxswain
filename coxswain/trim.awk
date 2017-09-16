BEGIN {
    buf = "";
}

{
    if (match($0,/ {20}/)) {
        match($0,/[^ ]/);
        buf = buf " " substr($0,RSTART,length($0));
    } else {
	print buf;
        buf = $0;
    }
}

END {
    print buf;
}
