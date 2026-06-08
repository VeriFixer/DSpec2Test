
method {:test} Test5() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 6 - TIME: 6.2309017 s