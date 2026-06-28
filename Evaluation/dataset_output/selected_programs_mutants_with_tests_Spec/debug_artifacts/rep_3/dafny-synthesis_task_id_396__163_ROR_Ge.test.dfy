// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

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
