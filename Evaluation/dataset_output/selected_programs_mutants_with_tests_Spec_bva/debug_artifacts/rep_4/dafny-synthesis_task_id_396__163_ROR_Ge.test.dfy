// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

method {:test} Test17() {
expect |"\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}"[0] == "\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}"[|"\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}"| - 1];
}
method {:test} Test18() {
expect |"\U{0002}a\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}a\0");
expect r0 <==> "\U{0002}a\0"[0] == "\U{0002}a\0"[|"\U{0002}a\0"| - 1];
}

// REPEAT 4 - TIME: 16.5328736 s
