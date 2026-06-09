
method {:test} Test23() {
expect |"\0\U{0002}\U{0004}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}\U{0004}\0");
expect r0 <==> "\0\U{0002}\U{0004}\0"[0] == "\0\U{0002}\U{0004}\0"[|"\0\U{0002}\U{0004}\0"| - 1];
}
method {:test} Test24() {
expect |"\U{0002}\0aa\n\U{0004}aaaaaaaaaa\U{0006}\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0aa\n\U{0004}aaaaaaaaaa\U{0006}\U{0008}");
expect r0 <==> "\U{0002}\0aa\n\U{0004}aaaaaaaaaa\U{0006}\U{0008}"[0] == "\U{0002}\0aa\n\U{0004}aaaaaaaaaa\U{0006}\U{0008}"[|"\U{0002}\0aa\n\U{0004}aaaaaaaaaa\U{0006}\U{0008}"| - 1];
}

// REPEAT 7 - TIME: 14.7587813 s