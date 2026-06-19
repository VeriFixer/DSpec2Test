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

method {:test} Test32() {
expect |"\U{0001}aaaaaa"| == |"?aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}aaaaaa", "?aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}aaaaaa"| ==> "\U{0001}aaaaaa"[n] == "?aaaaaa"[n] || "?aaaaaa"[n] == '?';
}
method {:test} Test33() {
expect |"aaaaaaaaa\U{0010}\0\U{0006}aaaaaaaaaaaaa\U{000E}aa"| == |"a\U{0008}a\U{0004}aaaaaa\U{0002}aaaaaaa\U{000C}aa\naaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\U{0010}\0\U{0006}aaaaaaaaaaaaa\U{000E}aa", "a\U{0008}a\U{0004}aaaaaa\U{0002}aaaaaaa\U{000C}aa\naaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\U{0010}\0\U{0006}aaaaaaaaaaaaa\U{000E}aa"| ==> "aaaaaaaaa\U{0010}\0\U{0006}aaaaaaaaaaaaa\U{000E}aa"[n] == "a\U{0008}a\U{0004}aaaaaa\U{0002}aaaaaaa\U{000C}aa\naaaaaa"[n] || "a\U{0008}a\U{0004}aaaaaa\U{0002}aaaaaaa\U{000C}aa\naaaaaa"[n] == '?';
}

// REPEAT 8 - TIME: 20.2897273 s
