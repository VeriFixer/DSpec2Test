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

method {:test} Test18() {
expect |"\U{0002}a\0a"| == |"\U{0002}a\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}a\0a", "\U{0002}a\0a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}a\0a"| ==> "\U{0002}a\0a"[n] == "\U{0002}a\0a"[n] || "\U{0002}a\0a"[n] == '?';
}
method {:test} Test19() {
expect |"\U{0006}aaaaaaa\0aaaaaaaaaaaaaaaaaaaaa"| == |"\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}aaaaaaa\0aaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}aaaaaaa\0aaaaaaaaaaaaaaaaaaaaa"| ==> "\U{0006}aaaaaaa\0aaaaaaaaaaaaaaaaaaaaa"[n] == "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaa"[n] || "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 10 - TIME: 16.2968812 s
