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
    break;
    if s[i] != p[i] && p[i] != '?' {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method {:test} Test0() {
expect |"a"| == |"a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a", "a");
expect r0 <==> forall n :: 0 <= n < |"a"| ==> "a"[n] == "a"[n] || "a"[n] == '?';
}
method {:test} Test1() {
expect |"aaaaaaaaa\0"| == |"aaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\0", "aaaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\0"| ==> "aaaaaaaaa\0"[n] == "aaaaaaaaa\U{0002}"[n] || "aaaaaaaaa\U{0002}"[n] == '?';
}
method {:test} Test2() {
expect |"aaaaaaaaa\0"| == |"aaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\0", "aaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\0"| ==> "aaaaaaaaa\0"[n] == "aaaaaaaaa\0"[n] || "aaaaaaaaa\0"[n] == '?';
}

// REPEAT 1 - TIME: 2.9100925 s
