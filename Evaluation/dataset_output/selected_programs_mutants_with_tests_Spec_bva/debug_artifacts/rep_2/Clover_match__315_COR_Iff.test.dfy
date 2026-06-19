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

method {:test} Test20() {
expect |"a\0a"| == |"a\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0a", "a\0a");
expect r0 <==> forall n :: 0 <= n < |"a\0a"| ==> "a\0a"[n] == "a\0a"[n] || "a\0a"[n] == '?';
}
method {:test} Test21() {
expect |"\U{0008}\U{0002}aa\U{0006}a\n"| == |"a\0aaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}\U{0002}aa\U{0006}a\n", "a\0aaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}\U{0002}aa\U{0006}a\n"| ==> "\U{0008}\U{0002}aa\U{0006}a\n"[n] == "a\0aaaa\U{0004}"[n] || "a\0aaaa\U{0004}"[n] == '?';
}

// REPEAT 2 - TIME: 13.5034956 s
