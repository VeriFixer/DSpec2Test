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
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test19() {
expect |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaa"[n] || "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test20() {
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaa"[n] || "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 7 - TIME: 11.9467539 s
