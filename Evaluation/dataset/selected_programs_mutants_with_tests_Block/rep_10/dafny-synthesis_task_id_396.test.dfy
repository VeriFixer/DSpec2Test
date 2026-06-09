
method {:test} Test9() {
expect |"\U{0002}aaa\U{0004}aaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaa\U{0004}aaaaaaa\0");
expect r0 <==> "\U{0002}aaa\U{0004}aaaaaaa\0"[0] == "\U{0002}aaa\U{0004}aaaaaaa\0"[|"\U{0002}aaa\U{0004}aaaaaaa\0"| - 1];
}

// REPEAT 10 - TIME: 9.1612815 s