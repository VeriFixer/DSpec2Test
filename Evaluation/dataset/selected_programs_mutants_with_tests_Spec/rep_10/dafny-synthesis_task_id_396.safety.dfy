method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test18() {
expect |"\0\U{0002}aaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaa\0");
expect r0 <==> "\0\U{0002}aaa\0"[0] == "\0\U{0002}aaa\0"[|"\0\U{0002}aaa\0"| - 1];
}
method {:test} Test19() {
expect |"\U{0016}\U{0002}aaa\na\U{0006}a\U{000C}aaaaaaa\U{0004}a\U{0010}aa\U{0008}aaaaa\U{000E}aaaaaaaaaa\U{0012}\U{0014}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0016}\U{0002}aaa\na\U{0006}a\U{000C}aaaaaaa\U{0004}a\U{0010}aa\U{0008}aaaaa\U{000E}aaaaaaaaaa\U{0012}\U{0014}\0");
expect r0 <==> "\U{0016}\U{0002}aaa\na\U{0006}a\U{000C}aaaaaaa\U{0004}a\U{0010}aa\U{0008}aaaaa\U{000E}aaaaaaaaaa\U{0012}\U{0014}\0"[0] == "\U{0016}\U{0002}aaa\na\U{0006}a\U{000C}aaaaaaa\U{0004}a\U{0010}aa\U{0008}aaaaa\U{000E}aaaaaaaaaa\U{0012}\U{0014}\0"[|"\U{0016}\U{0002}aaa\na\U{0006}a\U{000C}aaaaaaa\U{0004}a\U{0010}aa\U{0008}aaaaa\U{000E}aaaaaaaaaa\U{0012}\U{0014}\0"| - 1];
}

// REPEAT 10 - TIME: 15.6726073 s
