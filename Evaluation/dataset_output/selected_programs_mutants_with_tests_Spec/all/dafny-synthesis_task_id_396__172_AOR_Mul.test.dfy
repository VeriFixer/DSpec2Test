// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] == s[|s| * 1];
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

// REPEAT 1 - TIME: 3.1702736 s

method {:test} Test2() {
expect |"\0aaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaa\0");
expect r0 <==> "\0aaaaa\0"[0] == "\0aaaaa\0"[|"\0aaaaa\0"| - 1];
}
method {:test} Test3() {
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> "\U{0002}aaaaaaaaaaaaaaaaaaaa\0"[0] == "\U{0002}aaaaaaaaaaaaaaaaaaaa\0"[|"\U{0002}aaaaaaaaaaaaaaaaaaaa\0"| - 1];
}

// REPEAT 2 - TIME: 4.64309 s

method {:test} Test4() {
expect |"\0aaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaa\0");
expect r0 <==> "\0aaaaaa\0"[0] == "\0aaaaaa\0"[|"\0aaaaaa\0"| - 1];
}
method {:test} Test5() {
expect |"\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}");
expect r0 <==> "\0\U{0002}"[0] == "\0\U{0002}"[|"\0\U{0002}"| - 1];
}

// REPEAT 3 - TIME: 5.8391333 s

method {:test} Test6() {
expect |"\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0");
expect r0 <==> "\0"[0] == "\0"[|"\0"| - 1];
}
method {:test} Test7() {
expect |"\U{0004}\U{0002}aaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\U{0002}aaaaa\0");
expect r0 <==> "\U{0004}\U{0002}aaaaa\0"[0] == "\U{0004}\U{0002}aaaaa\0"[|"\U{0004}\U{0002}aaaaa\0"| - 1];
}

// REPEAT 4 - TIME: 7.0272411 s

method {:test} Test8() {
expect |"\0a\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0a\0");
expect r0 <==> "\0a\0"[0] == "\0a\0"[|"\0a\0"| - 1];
}
method {:test} Test9() {
expect |"\U{0004}\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\U{0002}\0");
expect r0 <==> "\U{0004}\U{0002}\0"[0] == "\U{0004}\U{0002}\0"[|"\U{0004}\U{0002}\0"| - 1];
}

// REPEAT 5 - TIME: 8.1129596 s

method {:test} Test10() {
expect |"\0aaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaa\0");
expect r0 <==> "\0aaa\0"[0] == "\0aaa\0"[|"\0aaa\0"| - 1];
}
method {:test} Test11() {
expect |"\U{0004}\U{0002}aaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\U{0002}aaaaaaaaaaa\0");
expect r0 <==> "\U{0004}\U{0002}aaaaaaaaaaa\0"[0] == "\U{0004}\U{0002}aaaaaaaaaaa\0"[|"\U{0004}\U{0002}aaaaaaaaaaa\0"| - 1];
}

// REPEAT 6 - TIME: 9.1894866 s

method {:test} Test12() {
expect |"\0\U{0002}aa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aa\0");
expect r0 <==> "\0\U{0002}aa\0"[0] == "\0\U{0002}aa\0"[|"\0\U{0002}aa\0"| - 1];
}
method {:test} Test13() {
expect |"\U{0002}aaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaa\0");
expect r0 <==> "\U{0002}aaa\0"[0] == "\U{0002}aaa\0"[|"\U{0002}aaa\0"| - 1];
}

// REPEAT 7 - TIME: 10.3957632 s

method {:test} Test14() {
expect |"\0\U{0002}aaa\U{0004}\U{0006}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaa\U{0004}\U{0006}\0");
expect r0 <==> "\0\U{0002}aaa\U{0004}\U{0006}\0"[0] == "\0\U{0002}aaa\U{0004}\U{0006}\0"[|"\0\U{0002}aaa\U{0004}\U{0006}\0"| - 1];
}
method {:test} Test15() {
expect |"\U{0004}\0a\U{0002}a\U{0006}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\0a\U{0002}a\U{0006}");
expect r0 <==> "\U{0004}\0a\U{0002}a\U{0006}"[0] == "\U{0004}\0a\U{0002}a\U{0006}"[|"\U{0004}\0a\U{0002}a\U{0006}"| - 1];
}

// REPEAT 8 - TIME: 11.4424795 s

method {:test} Test16() {
expect |"\0aa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aa\0");
expect r0 <==> "\0aa\0"[0] == "\0aa\0"[|"\0aa\0"| - 1];
}
method {:test} Test17() {
expect |"\U{0008}\0aa\U{0002}\U{0004}\U{0006}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0008}\0aa\U{0002}\U{0004}\U{0006}");
expect r0 <==> "\U{0008}\0aa\U{0002}\U{0004}\U{0006}"[0] == "\U{0008}\0aa\U{0002}\U{0004}\U{0006}"[|"\U{0008}\0aa\U{0002}\U{0004}\U{0006}"| - 1];
}

// REPEAT 9 - TIME: 12.7074731 s

method {:test} Test18() {
expect |"\0\U{0002}aaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaa\0");
expect r0 <==> "\0\U{0002}aaa\0"[0] == "\0\U{0002}aaa\0"[|"\0\U{0002}aaa\0"| - 1];
}
method {:test} Test19() {
expect |"\U{0004}\0a\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\0a\U{0002}");
expect r0 <==> "\U{0004}\0a\U{0002}"[0] == "\U{0004}\0a\U{0002}"[|"\U{0004}\0a\U{0002}"| - 1];
}

// REPEAT 10 - TIME: 13.8934482 s
