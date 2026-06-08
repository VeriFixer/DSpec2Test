
method {:test} Test1() {
var r0 := CountNonEmptySubstrings("aa\0");
expect r0 >= 0;
expect r0 == |"aa\0"| * (|"aa\0"| + 1) / 2;
}

// REPEAT 2 - TIME: 3.8955755 s