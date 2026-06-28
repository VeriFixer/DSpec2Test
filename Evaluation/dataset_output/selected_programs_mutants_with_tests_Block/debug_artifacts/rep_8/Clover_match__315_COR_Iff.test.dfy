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
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test22() {
expect |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"| == |"aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaa\0aa", "aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] == "aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[n] || "aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[n] == '?';
}
method {:test} Test23() {
expect |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"| == |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaa\0aa", "aaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] == "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] || "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] == '?';
}

// REPEAT 8 - TIME: 13.4887155 s
