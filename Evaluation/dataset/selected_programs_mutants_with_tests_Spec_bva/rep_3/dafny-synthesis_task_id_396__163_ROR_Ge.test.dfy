// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

method {:test} Test15() {
expect |"\0\U{0002}a\U{0004}aaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}a\U{0004}aaaaaaaaaaa\0");
expect r0 <==> "\0\U{0002}a\U{0004}aaaaaaaaaaa\0"[0] == "\0\U{0002}a\U{0004}aaaaaaaaaaa\0"[|"\0\U{0002}a\U{0004}aaaaaaaaaaa\0"| - 1];
}
method {:test} Test16() {
expect |"\U{0002}\0aa\U{0008}aa\U{0004}aaaaaaa\U{0006}\n"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0aa\U{0008}aa\U{0004}aaaaaaa\U{0006}\n");
expect r0 <==> "\U{0002}\0aa\U{0008}aa\U{0004}aaaaaaa\U{0006}\n"[0] == "\U{0002}\0aa\U{0008}aa\U{0004}aaaaaaa\U{0006}\n"[|"\U{0002}\0aa\U{0008}aa\U{0004}aaaaaaa\U{0006}\n"| - 1];
}

// REPEAT 3 - TIME: 10.2364299 s
