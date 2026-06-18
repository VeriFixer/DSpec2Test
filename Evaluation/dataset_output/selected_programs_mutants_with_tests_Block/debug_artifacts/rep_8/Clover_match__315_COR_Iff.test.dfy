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

method {:test} Test21() {
expect |"aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"| == |"aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a", "aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a");
expect r0 <==> forall n :: 0 <= n < |"aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"| ==> "aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"[n] == "aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"[n] || "aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"[n] == '?';
}
method {:test} Test22() {
expect |"aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{000C}"| == |"aa\0\U{0004}aaaaaaaaaaaaaaaaa\U{0006}aaa\naaa\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{000C}", "aa\0\U{0004}aaaaaaaaaaaaaaaaa\U{0006}aaa\naaa\U{000E}");
expect r0 <==> forall n :: 0 <= n < |"aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{000C}"| ==> "aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{000C}"[n] == "aa\0\U{0004}aaaaaaaaaaaaaaaaa\U{0006}aaa\naaa\U{000E}"[n] || "aa\0\U{0004}aaaaaaaaaaaaaaaaa\U{0006}aaa\naaa\U{000E}"[n] == '?';
}
method {:test} Test23() {
expect |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n"| == |"aa\0\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}aaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n", "aa\0\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}aaaa");
expect r0 <==> forall n :: 0 <= n < |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n"| ==> "aa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n"[n] == "aa\0\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}aaaa"[n] || "aa\0\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}aaaa"[n] == '?';
}

// REPEAT 8 - TIME: 14.1539001 s
