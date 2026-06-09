method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test0() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - 1];
}

// REPEAT 1 - TIME: 2.1858466 s

method {:test} Test1() {
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[0] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[|"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| - 1];
}

// REPEAT 2 - TIME: 2.9110209 s

method {:test} Test2() {
expect |"\U{0002}aaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaaaa\0");
expect r0 <==> "\U{0002}aaaaaaaaaa\0"[0] == "\U{0002}aaaaaaaaaa\0"[|"\U{0002}aaaaaaaaaa\0"| - 1];
}

// REPEAT 3 - TIME: 3.8124703 s

method {:test} Test3() {
expect |"\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect r0 <==> "\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[0] == "\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[|"\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| - 1];
}

// REPEAT 4 - TIME: 4.4559717 s

method {:test} Test4() {
expect |"\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0004}");
expect r0 <==> "\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0004}"[0] == "\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0004}"[|"\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0004}"| - 1];
}

// REPEAT 5 - TIME: 5.2342295 s

method {:test} Test5() {
expect |"\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}");
expect r0 <==> "\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}"[0] == "\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}"[|"\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}a\U{0008}"| - 1];
}

// REPEAT 6 - TIME: 6.049744 s

method {:test} Test6() {
expect |"\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}");
expect r0 <==> "\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}"[0] == "\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}"[|"\0aa\naaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa\U{0006}\U{0008}"| - 1];
}

// REPEAT 7 - TIME: 6.8831114 s

method {:test} Test7() {
expect |"\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}");
expect r0 <==> "\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}"[0] == "\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}"[|"\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}"| - 1];
}

// REPEAT 8 - TIME: 7.6137636 s

method {:test} Test8() {
expect |"\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> "\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}"[0] == "\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}"[|"\0aa\U{0008}aaaaaaaa\U{0002}aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0006}"| - 1];
}

// REPEAT 9 - TIME: 8.3202513 s

method {:test} Test9() {
expect |"\U{0002}aaa\U{0004}aaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaa\U{0004}aaaaaaa\0");
expect r0 <==> "\U{0002}aaa\U{0004}aaaaaaa\0"[0] == "\U{0002}aaa\U{0004}aaaaaaa\0"[|"\U{0002}aaa\U{0004}aaaaaaa\0"| - 1];
}

// REPEAT 10 - TIME: 9.1612815 s
