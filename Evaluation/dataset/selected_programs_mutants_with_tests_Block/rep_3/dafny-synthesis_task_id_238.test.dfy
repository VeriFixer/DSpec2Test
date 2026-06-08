
method {:test} Test2() {
var r0 := CountNonEmptySubstrings("aaaa");
expect r0 >= 0;
expect r0 == |"aaaa"| * (|"aaaa"| + 1) / 2;
}

// REPEAT 3 - TIME: 3.9646035 s