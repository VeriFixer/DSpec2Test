// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

method {:test} Test3() {
expect |"\0aaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaa\U{0002}"[0] == "\0aaaaaaa\U{0002}"[|"\0aaaaaaa\U{0002}"| - 1];
}

// REPEAT 4 - TIME: 5.2513557 s
