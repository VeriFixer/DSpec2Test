// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] == s[1];
}


method {:test} Test0() {
expect |"\0aaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaa\U{0002}"[0] == "\0aaaaaaa\U{0002}"[|"\0aaaaaaa\U{0002}"| - 1];
}

// REPEAT 1 - TIME: 3.0706453 s

method {:test} Test1() {
expect |"\U{0002}aaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaa\0");
expect r0 <==> "\U{0002}aaaaaaa\0"[0] == "\U{0002}aaaaaaa\0"[|"\U{0002}aaaaaaa\0"| - 1];
}

// REPEAT 2 - TIME: 4.0475599 s

method {:test} Test2() {
expect |"\U{0002}aaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaa\0");
expect r0 <==> "\U{0002}aaaaa\0"[0] == "\U{0002}aaaaa\0"[|"\U{0002}aaaaa\0"| - 1];
}

// REPEAT 3 - TIME: 4.9361015 s

method {:test} Test3() {
expect |"\U{0002}aaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaa\0");
expect r0 <==> "\U{0002}aaaaaa\0"[0] == "\U{0002}aaaaaa\0"[|"\U{0002}aaaaaa\0"| - 1];
}

// REPEAT 4 - TIME: 5.8914281 s

method {:test} Test4() {
expect |"\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}");
expect r0 <==> "\0\U{0002}"[0] == "\0\U{0002}"[|"\0\U{0002}"| - 1];
}

// REPEAT 5 - TIME: 6.685798 s

method {:test} Test5() {
expect |"\U{0002}aaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}");
expect r0 <==> "\U{0002}aaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}"[0] == "\U{0002}aaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}"[|"\U{0002}aaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}"| - 1];
}

// REPEAT 6 - TIME: 7.6281656 s

method {:test} Test6() {
expect |"\U{0006}aaaaaa\U{0002}\U{0004}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0006}aaaaaa\U{0002}\U{0004}\0");
expect r0 <==> "\U{0006}aaaaaa\U{0002}\U{0004}\0"[0] == "\U{0006}aaaaaa\U{0002}\U{0004}\0"[|"\U{0006}aaaaaa\U{0002}\U{0004}\0"| - 1];
}

// REPEAT 7 - TIME: 8.4817131 s

method {:test} Test7() {
expect |"\U{0002}a\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}a\0");
expect r0 <==> "\U{0002}a\0"[0] == "\U{0002}a\0"[|"\U{0002}a\0"| - 1];
}

// REPEAT 8 - TIME: 9.349409 s

method {:test} Test8() {
expect |"\U{0002}\0\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0\U{0004}");
expect r0 <==> "\U{0002}\0\U{0004}"[0] == "\U{0002}\0\U{0004}"[|"\U{0002}\0\U{0004}"| - 1];
}

// REPEAT 9 - TIME: 10.3403926 s

method {:test} Test9() {
expect |"\U{0004}a\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}a\0\U{0002}");
expect r0 <==> "\U{0004}a\0\U{0002}"[0] == "\U{0004}a\0\U{0002}"[|"\U{0004}a\0\U{0002}"| - 1];
}

// REPEAT 10 - TIME: 11.0666969 s
