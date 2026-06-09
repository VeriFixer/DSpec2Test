method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test5() {
expect |"\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}");
expect r0 <==> "\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}"[0] == "\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}"[|"\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}"| - 1];
}

// REPEAT 6 - TIME: 6.049744 s
