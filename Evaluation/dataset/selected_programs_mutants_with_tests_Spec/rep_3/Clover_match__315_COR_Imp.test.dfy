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
    if s[i] != p[i] ==> p[i] != '?' {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method {:test} Test4() {
expect |"\U{0003}a\U{0001}"| == |"?a?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0003}a\U{0001}", "?a?");
expect r0 <==> forall n :: 0 <= n < |"\U{0003}a\U{0001}"| ==> "\U{0003}a\U{0001}"[n] == "?a?"[n] || "?a?"[n] == '?';
}
method {:test} Test5() {
expect |"\U{0002}aaaaaaaaaaaa\U{0004}\0"| == |"aaaaaaaaaaaaa\U{0006}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaaaaaaaaaaa\U{0004}\0", "aaaaaaaaaaaaa\U{0006}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaaaaaaaaaaa\U{0004}\0"| ==> "\U{0002}aaaaaaaaaaaa\U{0004}\0"[n] == "aaaaaaaaaaaaa\U{0006}a"[n] || "aaaaaaaaaaaaa\U{0006}a"[n] == '?';
}

// REPEAT 3 - TIME: 5.3205961 s
