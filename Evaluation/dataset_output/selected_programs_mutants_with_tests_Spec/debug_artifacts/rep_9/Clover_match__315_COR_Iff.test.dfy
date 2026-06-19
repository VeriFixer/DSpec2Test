// Clover_match.dfy

method {:testEntry} Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall n :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
  {
    if s[i] != p[i] <==> p[i] != '?' {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method {:test} Test16() {
expect |"aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"| == |"aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n", "aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"| ==> "aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"[n] == "aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"[n] || "aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"[n] == '?';
}
method {:test} Test17() {
expect |"aaaaaaaaaaaaa\U{0008}\0aaaaaaa\U{000C}\U{000E}"| == |"aaaaaaaaaaaaa\n\U{0002}aaaa\U{0004}aaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\U{0008}\0aaaaaaa\U{000C}\U{000E}", "aaaaaaaaaaaaa\n\U{0002}aaaa\U{0004}aaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\U{0008}\0aaaaaaa\U{000C}\U{000E}"| ==> "aaaaaaaaaaaaa\U{0008}\0aaaaaaa\U{000C}\U{000E}"[n] == "aaaaaaaaaaaaa\n\U{0002}aaaa\U{0004}aaa\U{0006}"[n] || "aaaaaaaaaaaaa\n\U{0002}aaaa\U{0004}aaa\U{0006}"[n] == '?';
}

// REPEAT 9 - TIME: 11.620494 s
