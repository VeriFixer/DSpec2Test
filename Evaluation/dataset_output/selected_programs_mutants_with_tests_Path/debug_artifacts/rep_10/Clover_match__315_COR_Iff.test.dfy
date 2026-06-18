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

method {:test} Test27() {
expect |"aaaaaaaaaa\0a\U{0004}\U{0002}"| == |"aaaaaaaaaa\0a\U{0004}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaa\0a\U{0004}\U{0002}", "aaaaaaaaaa\0a\U{0004}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaa\0a\U{0004}\U{0002}"| ==> "aaaaaaaaaa\0a\U{0004}\U{0002}"[n] == "aaaaaaaaaa\0a\U{0004}\U{0002}"[n] || "aaaaaaaaaa\0a\U{0004}\U{0002}"[n] == '?';
}
method {:test} Test28() {
expect |"aaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa\U{0004}"| == |"aaaaaaaaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa\U{0004}", "aaaaaaaaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa\U{0004}"| ==> "aaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa\U{0004}"[n] == "aaaaaaaaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}"[n] || "aaaaaaaaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}"[n] == '?';
}
method {:test} Test29() {
expect |"aaa\0aaaaaaaaaaaaaa\U{0002}\U{0004}a"| == |"aaa\U{0006}aaaaaaaaaaaaaa\U{0002}\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\0aaaaaaaaaaaaaa\U{0002}\U{0004}a", "aaa\U{0006}aaaaaaaaaaaaaa\U{0002}\U{0004}a");
expect r0 <==> forall n :: 0 <= n < |"aaa\0aaaaaaaaaaaaaa\U{0002}\U{0004}a"| ==> "aaa\0aaaaaaaaaaaaaa\U{0002}\U{0004}a"[n] == "aaa\U{0006}aaaaaaaaaaaaaa\U{0002}\U{0004}a"[n] || "aaa\U{0006}aaaaaaaaaaaaaa\U{0002}\U{0004}a"[n] == '?';
}

// REPEAT 10 - TIME: 922.2051718 s
