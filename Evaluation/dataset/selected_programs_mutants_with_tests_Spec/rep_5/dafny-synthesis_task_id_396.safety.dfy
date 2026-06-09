method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test8() {
expect |"\0aaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\0");
expect r0 <==> "\0aaaaaaa\0"[0] == "\0aaaaaaa\0"[|"\0aaaaaaa\0"| - 1];
}
method {:test} Test9() {
expect |"\U{0002}\0aaaaaa\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0aaaaaa\U{0004}");
expect r0 <==> "\U{0002}\0aaaaaa\U{0004}"[0] == "\U{0002}\0aaaaaa\U{0004}"[|"\U{0002}\0aaaaaa\U{0004}"| - 1];
}

// REPEAT 5 - TIME: 7.8891796 s
