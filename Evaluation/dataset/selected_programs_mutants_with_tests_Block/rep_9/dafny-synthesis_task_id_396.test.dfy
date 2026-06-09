
method {:test} Test8() {
expect |"\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> "\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}"[0] == "\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}"[|"\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}"| - 1];
}

// REPEAT 9 - TIME: 8.3202513 s