
method {:test} Test6() {
expect |"\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}");
expect r0 <==> "\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}"[0] == "\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}"[|"\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}"| - 1];
}

// REPEAT 7 - TIME: 6.8831114 s