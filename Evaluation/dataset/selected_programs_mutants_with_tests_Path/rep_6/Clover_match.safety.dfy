method {:testEntry} Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall n :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
  {
    if s[i] != p[i] && p[i] != '?'
    {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method {:test} Test15() {
expect |"aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"| == |"aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n", "aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"| ==> "aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"[n] == "aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"[n] || "aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"[n] == '?';
}
method {:test} Test16() {
expect |"aa\0a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"| == |"aa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa", "aa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa");
expect r0 <==> forall n :: 0 <= n < |"aa\0a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"| ==> "aa\0a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] == "aa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] || "aa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] == '?';
}
method {:test} Test17() {
expect |"aa\0\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"| == |"aa\U{0002}\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa", "aa\U{0002}\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa");
expect r0 <==> forall n :: 0 <= n < |"aa\0\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"| ==> "aa\0\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] == "aa\U{0002}\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] || "aa\U{0002}\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] == '?';
}

// REPEAT 6 - TIME: 212.8175602 s
