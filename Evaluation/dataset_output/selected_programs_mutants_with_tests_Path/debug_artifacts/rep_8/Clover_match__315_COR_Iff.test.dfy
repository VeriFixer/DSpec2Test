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
expect |"\U{0002}aaa\0a"| == |"\U{0002}aaa\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaa\0a", "\U{0002}aaa\0a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaa\0a"| ==> "\U{0002}aaa\0a"[n] == "\U{0002}aaa\0a"[n] || "\U{0002}aaa\0a"[n] == '?';
}
method {:test} Test22() {
expect |"\0aaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}a\n"| == |"\U{000E}aaaaaaaaaaaaaaaaaa\U{0006}aa\U{0002}aaaaa\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}a\n", "\U{000E}aaaaaaaaaaaaaaaaaa\U{0006}aa\U{0002}aaaaa\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}a\n"| ==> "\0aaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}a\n"[n] == "\U{000E}aaaaaaaaaaaaaaaaaa\U{0006}aa\U{0002}aaaaa\U{000C}"[n] || "\U{000E}aaaaaaaaaaaaaaaaaa\U{0006}aa\U{0002}aaaaa\U{000C}"[n] == '?';
}

// REPEAT 8 - TIME: 521.4058599 s
