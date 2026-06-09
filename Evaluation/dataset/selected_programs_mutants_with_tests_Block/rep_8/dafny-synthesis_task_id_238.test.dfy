
method {:test} Test7() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 8 - TIME: 6.9283187 s