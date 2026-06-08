// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

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

// REPEAT 2 - TIME: 4.921995 s
