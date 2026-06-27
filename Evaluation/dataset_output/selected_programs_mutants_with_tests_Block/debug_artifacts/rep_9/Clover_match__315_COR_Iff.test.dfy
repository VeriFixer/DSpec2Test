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

method {:test} Test24() {
expect |"aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"| == |"aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}", "aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"[n] == "aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"[n] || "aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| == |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa", "aaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[n] == "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] || "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] == '?';
}
method {:test} Test26() {
expect |"aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"| == |"aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a", "aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"| ==> "aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"[n] == "aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"[n] || "aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"[n] == '?';
}

// REPEAT 9 - TIME: 19.3986792 s
