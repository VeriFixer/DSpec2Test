
method {:test} Test14() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a\U{0004}"| * (|"\U{0002}\0a\U{0004}"| + 1) / 2;
}

// REPEAT 8 - TIME: 11.854032 s