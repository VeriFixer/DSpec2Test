// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] != s[|s| - 1];
}


method {:test} Test0() {
expect |"\0aaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\0");
expect r0 <==> "\0aaaaaaa\0"[0] == "\0aaaaaaa\0"[|"\0aaaaaaa\0"| - 1];
}
method {:test} Test1() {
expect |"\0aaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaa\U{0002}"[0] == "\0aaaaaaa\U{0002}"[|"\0aaaaaaa\U{0002}"| - 1];
}

// REPEAT 1 - TIME: 3.0747297 s

method {:test} Test2() {
expect |"\0aaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaa\0");
expect r0 <==> "\0aaaaa\0"[0] == "\0aaaaa\0"[|"\0aaaaa\0"| - 1];
}
method {:test} Test3() {
expect |"\0aaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaa\U{0002}");
expect r0 <==> "\0aaaaa\U{0002}"[0] == "\0aaaaa\U{0002}"[|"\0aaaaa\U{0002}"| - 1];
}

// REPEAT 2 - TIME: 4.6814685 s

method {:test} Test4() {
expect |"\0a\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0a\0");
expect r0 <==> "\0a\0"[0] == "\0a\0"[|"\0a\0"| - 1];
}
method {:test} Test5() {
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> "\U{0002}aaaaaaaaaaaaaaaaaaaa\0"[0] == "\U{0002}aaaaaaaaaaaaaaaaaaaa\0"[|"\U{0002}aaaaaaaaaaaaaaaaaaaa\0"| - 1];
}

// REPEAT 3 - TIME: 6.1578781 s

method {:test} Test6() {
expect |"\U{0002}aaaaaa\0aaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaa\0aaaaaaaaa\U{0002}");
expect r0 <==> "\U{0002}aaaaaa\0aaaaaaaaa\U{0002}"[0] == "\U{0002}aaaaaa\0aaaaaaaaa\U{0002}"[|"\U{0002}aaaaaa\0aaaaaaaaa\U{0002}"| - 1];
}
method {:test} Test7() {
expect |"\0aaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaa\U{0002}");
expect r0 <==> "\0aaaaaa\U{0002}"[0] == "\0aaaaaa\U{0002}"[|"\0aaaaaa\U{0002}"| - 1];
}

// REPEAT 4 - TIME: 7.915949 s

method {:test} Test8() {
expect |"\0\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\0");
expect r0 <==> "\0\0"[0] == "\0\0"[|"\0\0"| - 1];
}
method {:test} Test9() {
expect |"\U{0006}aaaaa\U{0002}\U{0004}a\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0006}aaaaa\U{0002}\U{0004}a\0");
expect r0 <==> "\U{0006}aaaaa\U{0002}\U{0004}a\0"[0] == "\U{0006}aaaaa\U{0002}\U{0004}a\0"[|"\U{0006}aaaaa\U{0002}\U{0004}a\0"| - 1];
}

// REPEAT 5 - TIME: 9.2616437 s

method {:test} Test10() {
expect |"\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0");
expect r0 <==> "\0"[0] == "\0"[|"\0"| - 1];
}
method {:test} Test11() {
expect |"\0aaaaaa\U{0004}\U{0008}\naaaaaa\U{0006}a\U{000C}aa\U{0002}aaaaaaa\U{000E}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaa\U{0004}\U{0008}\naaaaaa\U{0006}a\U{000C}aa\U{0002}aaaaaaa\U{000E}");
expect r0 <==> "\0aaaaaa\U{0004}\U{0008}\naaaaaa\U{0006}a\U{000C}aa\U{0002}aaaaaaa\U{000E}"[0] == "\0aaaaaa\U{0004}\U{0008}\naaaaaa\U{0006}a\U{000C}aa\U{0002}aaaaaaa\U{000E}"[|"\0aaaaaa\U{0004}\U{0008}\naaaaaa\U{0006}a\U{000C}aa\U{0002}aaaaaaa\U{000E}"| - 1];
}

// REPEAT 6 - TIME: 10.5398709 s

method {:test} Test12() {
expect |"\n\0a\U{0002}aaa\U{0006}a\U{0004}aaaaaaa\U{0008}\n"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\n\0a\U{0002}aaa\U{0006}a\U{0004}aaaaaaa\U{0008}\n");
expect r0 <==> "\n\0a\U{0002}aaa\U{0006}a\U{0004}aaaaaaa\U{0008}\n"[0] == "\n\0a\U{0002}aaa\U{0006}a\U{0004}aaaaaaa\U{0008}\n"[|"\n\0a\U{0002}aaa\U{0006}a\U{0004}aaaaaaa\U{0008}\n"| - 1];
}
method {:test} Test13() {
expect |"\U{0010}\0aaaaa\U{0004}a\n\U{000C}aa\U{0006}aa\U{0008}a\U{000E}aaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0010}\0aaaaa\U{0004}a\n\U{000C}aa\U{0006}aa\U{0008}a\U{000E}aaa\U{0002}");
expect r0 <==> "\U{0010}\0aaaaa\U{0004}a\n\U{000C}aa\U{0006}aa\U{0008}a\U{000E}aaa\U{0002}"[0] == "\U{0010}\0aaaaa\U{0004}a\n\U{000C}aa\U{0006}aa\U{0008}a\U{000E}aaa\U{0002}"[|"\U{0010}\0aaaaa\U{0004}a\n\U{000C}aa\U{0006}aa\U{0008}a\U{000E}aaa\U{0002}"| - 1];
}

// REPEAT 7 - TIME: 11.7836549 s

method {:test} Test14() {
expect |"\0aaaaaa\U{0004}\U{0002}\na\U{0008}\U{0006}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaa\U{0004}\U{0002}\na\U{0008}\U{0006}\0");
expect r0 <==> "\0aaaaaa\U{0004}\U{0002}\na\U{0008}\U{0006}\0"[0] == "\0aaaaaa\U{0004}\U{0002}\na\U{0008}\U{0006}\0"[|"\0aaaaaa\U{0004}\U{0002}\na\U{0008}\U{0006}\0"| - 1];
}
method {:test} Test15() {
expect |"\U{0014}aaaaaa\U{0006}a\U{000C}aa\U{0004}a\U{0008}\U{0002}\na\U{000E}\U{0010}aa\U{0012}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0014}aaaaaa\U{0006}a\U{000C}aa\U{0004}a\U{0008}\U{0002}\na\U{000E}\U{0010}aa\U{0012}\0");
expect r0 <==> "\U{0014}aaaaaa\U{0006}a\U{000C}aa\U{0004}a\U{0008}\U{0002}\na\U{000E}\U{0010}aa\U{0012}\0"[0] == "\U{0014}aaaaaa\U{0006}a\U{000C}aa\U{0004}a\U{0008}\U{0002}\na\U{000E}\U{0010}aa\U{0012}\0"[|"\U{0014}aaaaaa\U{0006}a\U{000C}aa\U{0004}a\U{0008}\U{0002}\na\U{000E}\U{0010}aa\U{0012}\0"| - 1];
}

// REPEAT 8 - TIME: 13.2017506 s

method {:test} Test16() {
expect |"\0aaaaaa\U{0002}a\U{0004}aaaa\U{0006}aaaaaa\U{0008}\n\U{000C}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaa\U{0002}a\U{0004}aaaa\U{0006}aaaaaa\U{0008}\n\U{000C}\0");
expect r0 <==> "\0aaaaaa\U{0002}a\U{0004}aaaa\U{0006}aaaaaa\U{0008}\n\U{000C}\0"[0] == "\0aaaaaa\U{0002}a\U{0004}aaaa\U{0006}aaaaaa\U{0008}\n\U{000C}\0"[|"\0aaaaaa\U{0002}a\U{0004}aaaa\U{0006}aaaaaa\U{0008}\n\U{000C}\0"| - 1];
}
method {:test} Test17() {
expect |"\U{0004}\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\U{0002}\0");
expect r0 <==> "\U{0004}\U{0002}\0"[0] == "\U{0004}\U{0002}\0"[|"\U{0004}\U{0002}\0"| - 1];
}

// REPEAT 9 - TIME: 14.5448569 s

method {:test} Test18() {
expect |"\0\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\0");
expect r0 <==> "\0\0"[0] == "\0\0"[|"\0\0"| - 1];
}
method {:test} Test19() {
expect |"\U{001A}\0aaaaa\U{0006}a\U{000C}a\U{0008}\U{000E}aa\na\U{0010}\U{0004}\U{0014}aa\U{0016}\U{0018}\U{0002}\U{0012}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{001A}\0aaaaa\U{0006}a\U{000C}a\U{0008}\U{000E}aa\na\U{0010}\U{0004}\U{0014}aa\U{0016}\U{0018}\U{0002}\U{0012}");
expect r0 <==> "\U{001A}\0aaaaa\U{0006}a\U{000C}a\U{0008}\U{000E}aa\na\U{0010}\U{0004}\U{0014}aa\U{0016}\U{0018}\U{0002}\U{0012}"[0] == "\U{001A}\0aaaaa\U{0006}a\U{000C}a\U{0008}\U{000E}aa\na\U{0010}\U{0004}\U{0014}aa\U{0016}\U{0018}\U{0002}\U{0012}"[|"\U{001A}\0aaaaa\U{0006}a\U{000C}a\U{0008}\U{000E}aa\na\U{0010}\U{0004}\U{0014}aa\U{0016}\U{0018}\U{0002}\U{0012}"| - 1];
}

// REPEAT 10 - TIME: 15.7464222 s
