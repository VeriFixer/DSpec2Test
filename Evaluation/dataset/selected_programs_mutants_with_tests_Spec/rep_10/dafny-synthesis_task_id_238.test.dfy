
method {:test} Test9() {
var r0 := CountNonEmptySubstrings("\0aaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaa\U{0002}"| * (|"\0aaa\U{0002}"| + 1) / 2;
}

// REPEAT 10 - TIME: 9.9571444 s