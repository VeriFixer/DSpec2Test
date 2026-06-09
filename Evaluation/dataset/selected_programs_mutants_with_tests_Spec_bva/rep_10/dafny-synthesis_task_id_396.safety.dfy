method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test29() {
expect |"\0\U{0002}\U{0016}aa\U{0006}aaaaaaa\na\U{000C}a\U{000E}\U{0010}\U{0012}a\U{0014}aaaaa\U{0008}aaa\U{0004}aaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}\U{0016}aa\U{0006}aaaaaaa\na\U{000C}a\U{000E}\U{0010}\U{0012}a\U{0014}aaaaa\U{0008}aaa\U{0004}aaaaa\0");
expect r0 <==> "\0\U{0002}\U{0016}aa\U{0006}aaaaaaa\na\U{000C}a\U{000E}\U{0010}\U{0012}a\U{0014}aaaaa\U{0008}aaa\U{0004}aaaaa\0"[0] == "\0\U{0002}\U{0016}aa\U{0006}aaaaaaa\na\U{000C}a\U{000E}\U{0010}\U{0012}a\U{0014}aaaaa\U{0008}aaa\U{0004}aaaaa\0"[|"\0\U{0002}\U{0016}aa\U{0006}aaaaaaa\na\U{000C}a\U{000E}\U{0010}\U{0012}a\U{0014}aaaaa\U{0008}aaa\U{0004}aaaaa\0"| - 1];
}
method {:test} Test30() {
expect |"\U{0002}\U{0004}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\U{0004}\0");
expect r0 <==> "\U{0002}\U{0004}\0"[0] == "\U{0002}\U{0004}\0"[|"\U{0002}\U{0004}\0"| - 1];
}

// REPEAT 10 - TIME: 18.6674238 s
