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

method {:test} Test22() {
expect |"\U{0001}aa"| == |"?a?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}aa", "?a?");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}aa"| ==> "\U{0001}aa"[n] == "?a?"[n] || "?a?"[n] == '?';
}
method {:test} Test23() {
expect |"aa\0\U{0004}"| == |"a\U{0002}\U{0006}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0\U{0004}", "a\U{0002}\U{0006}a");
expect r0 <==> forall n :: 0 <= n < |"aa\0\U{0004}"| ==> "aa\0\U{0004}"[n] == "a\U{0002}\U{0006}a"[n] || "a\U{0002}\U{0006}a"[n] == '?';
}

// REPEAT 3 - TIME: 15.2118005 s
