// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

method {:test} Test10() {
expect |"\0aaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaa\0");
expect r0 <==> "\0aaaaaaaa\0"[0] == "\0aaaaaaaa\0"[|"\0aaaaaaaa\0"| - 1];
}
method {:test} Test11() {
expect |"\U{0004}\U{0002}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\U{0002}\0");
expect r0 <==> "\U{0004}\U{0002}\0"[0] == "\U{0004}\U{0002}\0"[|"\U{0004}\U{0002}\0"| - 1];
}

// REPEAT 6 - TIME: 9.7188861 s
