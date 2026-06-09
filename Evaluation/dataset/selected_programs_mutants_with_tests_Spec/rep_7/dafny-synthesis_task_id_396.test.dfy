
method {:test} Test12() {
expect |"\0\U{0002}aa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aa\0");
expect r0 <==> "\0\U{0002}aa\0"[0] == "\0\U{0002}aa\0"[|"\0\U{0002}aa\0"| - 1];
}
method {:test} Test13() {
expect |"\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0");
expect r0 <==> "\U{0002}\0"[0] == "\U{0002}\0"[|"\U{0002}\0"| - 1];
}

// REPEAT 7 - TIME: 10.162295 s