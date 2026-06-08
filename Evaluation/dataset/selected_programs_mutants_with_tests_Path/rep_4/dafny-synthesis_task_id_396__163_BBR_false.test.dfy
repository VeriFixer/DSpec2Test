// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := false;
}

method {:test} Test3() {
expect |"\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect r0 <==> "\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[0] == "\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[|"\0aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| - 1];
}

// REPEAT 4 - TIME: 6.6593927 s
