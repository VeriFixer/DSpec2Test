
method {:test} Test16() {
expect |"\0\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}\0");
expect r0 <==> "\0\U{0002}\0"[0] == "\0\U{0002}\0"[|"\0\U{0002}\0"| - 1];
}
method {:test} Test17() {
expect |"\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}");
expect r0 <==> "\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}"[0] == "\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}"[|"\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}"| - 1];
}

// REPEAT 9 - TIME: 12.3685967 s