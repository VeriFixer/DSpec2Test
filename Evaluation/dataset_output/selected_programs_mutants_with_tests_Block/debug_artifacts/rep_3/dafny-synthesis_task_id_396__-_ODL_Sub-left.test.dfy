// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] == s[1];
}

method {:test} Test2() {
expect |"\U{0002}aaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaa\0");
expect r0 <==> "\U{0002}aaaaa\0"[0] == "\U{0002}aaaaa\0"[|"\U{0002}aaaaa\0"| - 1];
}

// REPEAT 3 - TIME: 3.6263485 s
