// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

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

// REPEAT 3 - TIME: 5.468203 s
