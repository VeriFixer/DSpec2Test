
method {:test} Test6() {
var r0 := CountNonEmptySubstrings("\U{0002}\0aa");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aa"| * (|"\U{0002}\0aa"| + 1) / 2;
}

// REPEAT 7 - TIME: 7.3098927 s