method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test25() {
expect |"\0a\na\U{000C}\U{0006}\U{0004}a\U{0002}aaaa\U{0008}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0a\na\U{000C}\U{0006}\U{0004}a\U{0002}aaaa\U{0008}\0");
expect r0 <==> "\0a\na\U{000C}\U{0006}\U{0004}a\U{0002}aaaa\U{0008}\0"[0] == "\0a\na\U{000C}\U{0006}\U{0004}a\U{0002}aaaa\U{0008}\0"[|"\0a\na\U{000C}\U{0006}\U{0004}a\U{0002}aaaa\U{0008}\0"| - 1];
}
method {:test} Test26() {
expect |"\U{0004}aaa\U{0010}\U{0006}aa\U{0002}aaa\U{0008}a\na\U{000C}\U{000E}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}aaa\U{0010}\U{0006}aa\U{0002}aaa\U{0008}a\na\U{000C}\U{000E}\0");
expect r0 <==> "\U{0004}aaa\U{0010}\U{0006}aa\U{0002}aaa\U{0008}a\na\U{000C}\U{000E}\0"[0] == "\U{0004}aaa\U{0010}\U{0006}aa\U{0002}aaa\U{0008}a\na\U{000C}\U{000E}\0"[|"\U{0004}aaa\U{0010}\U{0006}aa\U{0002}aaa\U{0008}a\na\U{000C}\U{000E}\0"| - 1];
}

// REPEAT 8 - TIME: 16.0169703 s
