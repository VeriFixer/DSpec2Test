// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := false;
}

method {:test} Test5() {
expect |"\U{0002}aaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaa\0");
expect r0 <==> "\U{0002}aaaaaaaa\0"[0] == "\U{0002}aaaaaaaa\0"[|"\U{0002}aaaaaaaa\0"| - 1];
}

// REPEAT 6 - TIME: 7.151347 s
