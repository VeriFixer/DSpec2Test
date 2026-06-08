
method {:test} Test2() {
expect |"\U{0002}aaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaaaa\0");
expect r0 <==> "\U{0002}aaaaaaaaaa\0"[0] == "\U{0002}aaaaaaaaaa\0"[|"\U{0002}aaaaaaaaaa\0"| - 1];
}

// REPEAT 3 - TIME: 5.3999775 s