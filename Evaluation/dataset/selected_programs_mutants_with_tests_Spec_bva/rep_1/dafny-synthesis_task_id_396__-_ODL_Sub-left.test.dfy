// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] == s[1];
}

method {:test} Test0() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| - 1];
}
method {:test} Test1() {
expect |"\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0");
expect r0 <==> "\0"[0] == "\0"[|"\0"| - 1];
}
method {:test} Test2() {
expect |"\0\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\0");
expect r0 <==> "\0\0"[0] == "\0\0"[|"\0\0"| - 1];
}
method {:test} Test7() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - 1];
}
method {:test} Test8() {
expect |"\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}");
expect r0 <==> "\0\U{0002}"[0] == "\0\U{0002}"[|"\0\U{0002}"| - 1];
}

// REPEAT 1 - TIME: 8.3413785 s
