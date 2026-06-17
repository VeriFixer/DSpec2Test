// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] >= s[|s| - 1];
}

method {:test} Test17() {
expect |"\0aaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaa\0");
expect r0 <==> "\0aaaaaaaaaaa\0"[0] == "\0aaaaaaaaaaa\0"[|"\0aaaaaaaaaaa\0"| - 1];
}
method {:test} Test18() {
expect |"\0\U{0004}a\U{000C}aaaaaaaa\U{0006}aaa\U{0008}\naa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0004}a\U{000C}aaaaaaaa\U{0006}aaa\U{0008}\naa\U{0002}");
expect r0 <==> "\0\U{0004}a\U{000C}aaaaaaaa\U{0006}aaa\U{0008}\naa\U{0002}"[0] == "\0\U{0004}a\U{000C}aaaaaaaa\U{0006}aaa\U{0008}\naa\U{0002}"[|"\0\U{0004}a\U{000C}aaaaaaaa\U{0006}aaa\U{0008}\naa\U{0002}"| - 1];
}

// REPEAT 4 - TIME: 12.7768444 s
