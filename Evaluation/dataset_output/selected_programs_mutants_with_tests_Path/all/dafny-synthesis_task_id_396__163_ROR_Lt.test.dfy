// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] < s[|s| - 1];
}


method {:test} Test0() {
expect |"\0aaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaa\U{0002}"[0] == "\0aaaaaaa\U{0002}"[|"\0aaaaaaa\U{0002}"| - 1];
}

// REPEAT 1 - TIME: 2.4833813 s

method {:test} Test1() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - 1];
}

// REPEAT 2 - TIME: 3.4151614 s

method {:test} Test2() {
expect |"\0aaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaa\U{0002}"[0] == "\0aaaaaaa\U{0002}"[|"\0aaaaaaa\U{0002}"| - 1];
}

// REPEAT 3 - TIME: 4.2532897 s

method {:test} Test3() {
expect |"\0aaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaa\U{0002}"[0] == "\0aaaaaaa\U{0002}"[|"\0aaaaaaa\U{0002}"| - 1];
}

// REPEAT 4 - TIME: 5.2513557 s

method {:test} Test4() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - 1];
}

// REPEAT 5 - TIME: 6.2335615 s

method {:test} Test5() {
expect |"\U{0002}aaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaa\0");
expect r0 <==> "\U{0002}aaaaaaaa\0"[0] == "\U{0002}aaaaaaaa\0"[|"\U{0002}aaaaaaaa\0"| - 1];
}

// REPEAT 6 - TIME: 7.151347 s

method {:test} Test6() {
expect |"\U{0002}aaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaa\0");
expect r0 <==> "\U{0002}aaaaa\0"[0] == "\U{0002}aaaaa\0"[|"\U{0002}aaaaa\0"| - 1];
}

// REPEAT 7 - TIME: 7.7769846 s

method {:test} Test7() {
expect |"\U{0002}aaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaa\0");
expect r0 <==> "\U{0002}aaaaaa\0"[0] == "\U{0002}aaaaaa\0"[|"\U{0002}aaaaaa\0"| - 1];
}

// REPEAT 8 - TIME: 8.5808475 s

method {:test} Test8() {
expect |"\U{0002}aa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aa\0");
expect r0 <==> "\U{0002}aa\0"[0] == "\U{0002}aa\0"[|"\U{0002}aa\0"| - 1];
}

// REPEAT 9 - TIME: 9.4041773 s

method {:test} Test9() {
expect |"\U{0002}aa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aa\0");
expect r0 <==> "\U{0002}aa\0"[0] == "\U{0002}aa\0"[|"\U{0002}aa\0"| - 1];
}

// REPEAT 10 - TIME: 10.1143117 s
