method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test27() {
expect |"\0\U{0002}a\U{0010}a\U{0006}aaaaaaaaa\na\U{000E}aaaaaaaaa\U{0004}aaa\U{0008}aaa\U{000C}a\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}a\U{0010}a\U{0006}aaaaaaaaa\na\U{000E}aaaaaaaaa\U{0004}aaa\U{0008}aaa\U{000C}a\0");
expect r0 <==> "\0\U{0002}a\U{0010}a\U{0006}aaaaaaaaa\na\U{000E}aaaaaaaaa\U{0004}aaa\U{0008}aaa\U{000C}a\0"[0] == "\0\U{0002}a\U{0010}a\U{0006}aaaaaaaaa\na\U{000E}aaaaaaaaa\U{0004}aaa\U{0008}aaa\U{000C}a\0"[|"\0\U{0002}a\U{0010}a\U{0006}aaaaaaaaa\na\U{000E}aaaaaaaaa\U{0004}aaa\U{0008}aaa\U{000C}a\0"| - 1];
}
method {:test} Test28() {
expect |"\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}");
expect r0 <==> "\0\U{0002}"[0] == "\0\U{0002}"[|"\0\U{0002}"| - 1];
}

// REPEAT 9 - TIME: 18.2577222 s
