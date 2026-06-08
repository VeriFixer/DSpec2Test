
method {:test} Test1() {
var r0 := CountNonEmptySubstrings("aa");
expect r0 >= 0;
expect r0 == |"aa"| * (|"aa"| + 1) / 2;
}

// REPEAT 2 - TIME: 4.14729 s