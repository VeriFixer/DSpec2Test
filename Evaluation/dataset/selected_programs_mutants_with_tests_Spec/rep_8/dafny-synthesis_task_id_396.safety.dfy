method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test14() {
expect |"\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0");
expect r0 <==> "\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"[0] == "\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"[|"\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"| - 1];
}
method {:test} Test15() {
expect |"\U{0004}\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\U{0002}\0");
expect r0 <==> "\U{0004}\U{0002}\0"[0] == "\U{0004}\U{0002}\0"[|"\U{0004}\U{0002}\0"| - 1];
}

// REPEAT 8 - TIME: 13.2962599 s
