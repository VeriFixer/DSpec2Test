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

method {:test} Test6() {
expect |"\U{0002}\0a"| == |"\U{0002}\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0a", "\U{0002}\0a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0a"| ==> "\U{0002}\0a"[n] == "\U{0002}\0a"[n] || "\U{0002}\0a"[n] == '?';
}
method {:test} Test7() {
expect |"\0aa"| == |"\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa", "\U{0002}aa");
expect r0 <==> forall n :: 0 <= n < |"\0aa"| ==> "\0aa"[n] == "\U{0002}aa"[n] || "\U{0002}aa"[n] == '?';
}
method {:test} Test8() {
expect |"\0a"| == |"\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0a", "\0a");
expect r0 <==> forall n :: 0 <= n < |"\0a"| ==> "\0a"[n] == "\0a"[n] || "\0a"[n] == '?';
}

// REPEAT 3 - TIME: 6.2015728 s
