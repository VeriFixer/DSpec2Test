// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

method {:test} Test15() {
expect |"\0aaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaa\0");
expect r0 <==> "\0aaaaaaaaaa\0"[0] == "\0aaaaaaaaaa\0"[|"\0aaaaaaaaaa\0"| - 1];
}
method {:test} Test16() {
expect |"\U{0006}\0aaaaaa\U{0002}\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0006}\0aaaaaa\U{0002}\U{0004}");
expect r0 <==> "\U{0006}\0aaaaaa\U{0002}\U{0004}"[0] == "\U{0006}\0aaaaaa\U{0002}\U{0004}"[|"\U{0006}\0aaaaaa\U{0002}\U{0004}"| - 1];
}

// REPEAT 3 - TIME: 11.4718458 s
