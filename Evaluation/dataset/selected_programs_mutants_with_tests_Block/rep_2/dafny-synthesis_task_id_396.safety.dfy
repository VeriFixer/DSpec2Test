method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test1() {
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[0] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[|"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| - 1];
}

// REPEAT 2 - TIME: 2.9110209 s
