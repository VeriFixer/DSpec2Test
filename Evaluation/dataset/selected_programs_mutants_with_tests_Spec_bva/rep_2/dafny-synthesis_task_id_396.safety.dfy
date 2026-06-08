method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test13() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0002}aaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0002}aaaaaaaa\0");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0002}aaaaaaaa\0"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0002}aaaaaaaa\0"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0002}aaaaaaaa\0"| - 1];
}
method {:test} Test14() {
expect |"\U{0002}\0aaaaaaaaa\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0aaaaaaaaa\U{0004}");
expect r0 <==> "\U{0002}\0aaaaaaaaa\U{0004}"[0] == "\U{0002}\0aaaaaaaaa\U{0004}"[|"\U{0002}\0aaaaaaaaa\U{0004}"| - 1];
}

// REPEAT 2 - TIME: 9.4039759 s
