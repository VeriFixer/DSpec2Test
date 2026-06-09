// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := false;
}

method {:test} Test7() {
expect |"\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}");
expect r0 <==> "\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}"[0] == "\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}"[|"\0aaa\U{0006}aaaaaaaaaa\U{0004}\U{0002}"| - 1];
}

// REPEAT 8 - TIME: 11.1208669 s
