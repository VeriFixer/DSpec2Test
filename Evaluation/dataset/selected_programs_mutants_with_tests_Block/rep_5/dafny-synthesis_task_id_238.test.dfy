
method {:test} Test4() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 5 - TIME: 5.4297686 s