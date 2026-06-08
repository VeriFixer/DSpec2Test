
method {:test} Test19() {
expect |"\0\U{0002}aaaaaaaaaaaaaa\U{0006}\U{0008}aaa\naaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaaaaaaaaaaaaa\U{0006}\U{0008}aaa\naaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\0");
expect r0 <==> "\0\U{0002}aaaaaaaaaaaaaa\U{0006}\U{0008}aaa\naaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\0"[0] == "\0\U{0002}aaaaaaaaaaaaaa\U{0006}\U{0008}aaa\naaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\0"[|"\0\U{0002}aaaaaaaaaaaaaa\U{0006}\U{0008}aaa\naaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\0"| - 1];
}
method {:test} Test20() {
expect |"\U{0006}\U{0002}a\U{0004}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0006}\U{0002}a\U{0004}\0");
expect r0 <==> "\U{0006}\U{0002}a\U{0004}\0"[0] == "\U{0006}\U{0002}a\U{0004}\0"[|"\U{0006}\U{0002}a\U{0004}\0"| - 1];
}

// REPEAT 5 - TIME: 13.3017892 s