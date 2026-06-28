// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

method {:test} Test15() {
expect |"\0aaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaa\0");
expect r0 <==> "\0aaa\0"[0] == "\0aaa\0"[|"\0aaa\0"| - 1];
}
method {:test} Test16() {
expect |"\U{0006}\0\U{0002}a\U{0004}\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0006}\0\U{0002}a\U{0004}\U{0008}");
expect r0 <==> "\U{0006}\0\U{0002}a\U{0004}\U{0008}"[0] == "\U{0006}\0\U{0002}a\U{0004}\U{0008}"[|"\U{0006}\0\U{0002}a\U{0004}\U{0008}"| - 1];
}

// REPEAT 3 - TIME: 14.8963486 s
