method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test21() {
expect |"\0\U{0008}aa\U{0002}\U{0004}aaaaaa\U{0006}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0008}aa\U{0002}\U{0004}aaaaaa\U{0006}\0");
expect r0 <==> "\0\U{0008}aa\U{0002}\U{0004}aaaaaa\U{0006}\0"[0] == "\0\U{0008}aa\U{0002}\U{0004}aaaaaa\U{0006}\0"[|"\0\U{0008}aa\U{0002}\U{0004}aaaaaa\U{0006}\0"| - 1];
}
method {:test} Test22() {
expect |"\U{0004}\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\0\U{0002}");
expect r0 <==> "\U{0004}\0\U{0002}"[0] == "\U{0004}\0\U{0002}"[|"\U{0004}\0\U{0002}"| - 1];
}

// REPEAT 6 - TIME: 13.4300473 s
