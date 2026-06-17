// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] == s[1];
}


method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    result := s[0] == s[|s| - 1];
}

method {:test} Test0() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| - 1];
}
method {:test} Test1() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - 1];
}

// REPEAT 1 - TIME: 2.8327342 s

method {:test} Test2() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| - 1];
}
method {:test} Test3() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - 1];
}

// REPEAT 2 - TIME: 4.1851524 s

method {:test} Test4() {
expect |"\0aaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaa\0");
expect r0 <==> "\0aaaaaaaaaa\0"[0] == "\0aaaaaaaaaa\0"[|"\0aaaaaaaaaa\0"| - 1];
}
method {:test} Test5() {
expect |"\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}");
expect r0 <==> "\0\U{0002}"[0] == "\0\U{0002}"[|"\0\U{0002}"| - 1];
}

// REPEAT 3 - TIME: 5.6222377 s

method {:test} Test6() {
expect |"\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0");
expect r0 <==> "\0"[0] == "\0"[|"\0"| - 1];
}
method {:test} Test7() {
expect |"\0aaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaaaaaa\U{0002}"[0] == "\0aaaaaaaaaaa\U{0002}"[|"\0aaaaaaaaaaa\U{0002}"| - 1];
}

// REPEAT 4 - TIME: 7.1006737 s

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

// REPEAT 5 - TIME: 8.3956942 s

method {:test} Test10() {
expect |"\0aaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaa\0");
expect r0 <==> "\0aaaaaaaa\0"[0] == "\0aaaaaaaa\0"[|"\0aaaaaaaa\0"| - 1];
}
method {:test} Test11() {
expect |"\U{0004}\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\U{0002}\0");
expect r0 <==> "\U{0004}\U{0002}\0"[0] == "\U{0004}\U{0002}\0"[|"\U{0004}\U{0002}\0"| - 1];
}

// REPEAT 6 - TIME: 9.7188861 s

method {:test} Test12() {
expect |"\0\U{0002}aa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aa\0");
expect r0 <==> "\0\U{0002}aa\0"[0] == "\0\U{0002}aa\0"[|"\0\U{0002}aa\0"| - 1];
}
method {:test} Test13() {
expect |"\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0");
expect r0 <==> "\U{0002}\0"[0] == "\U{0002}\0"[|"\U{0002}\0"| - 1];
}

// REPEAT 7 - TIME: 10.9659585 s

method {:test} Test14() {
expect |"\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0");
expect r0 <==> "\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"[0] == "\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"[|"\0\U{0002}aaaaaaa\U{0006}aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"| - 1];
}
method {:test} Test15() {
expect |"\U{0004}\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\U{0002}\0");
expect r0 <==> "\U{0004}\U{0002}\0"[0] == "\U{0004}\U{0002}\0"[|"\U{0004}\U{0002}\0"| - 1];
}

// REPEAT 8 - TIME: 12.1729864 s

method {:test} Test16() {
expect |"\0\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}\0");
expect r0 <==> "\0\U{0002}\0"[0] == "\0\U{0002}\0"[|"\0\U{0002}\0"| - 1];
}
method {:test} Test17() {
expect |"\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}");
expect r0 <==> "\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}"[0] == "\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}"[|"\U{0002}\0a\U{0004}a\U{0008}aaa\n\U{000E}\U{0006}a\U{000C}"| - 1];
}

// REPEAT 9 - TIME: 13.4516861 s

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

// REPEAT 10 - TIME: 14.460641 s
