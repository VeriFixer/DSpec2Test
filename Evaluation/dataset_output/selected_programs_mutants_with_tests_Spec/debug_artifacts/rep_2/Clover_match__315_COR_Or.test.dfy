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
    if s[i] != p[i] || p[i] != '?' {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method {:test} Test2() {
expect |"aaaaaaaaa\U{0001}"| == |"aaaaaaaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\U{0001}", "aaaaaaaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\U{0001}"| ==> "aaaaaaaaa\U{0001}"[n] == "aaaaaaaaa?"[n] || "aaaaaaaaa?"[n] == '?';
}
method {:test} Test3() {
expect |"aaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"| == |"aaaaaaaa\U{0004}\0aaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}", "aaaaaaaa\U{0004}\0aaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"| ==> "aaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"[n] == "aaaaaaaa\U{0004}\0aaaaaaaaaaaa"[n] || "aaaaaaaa\U{0004}\0aaaaaaaaaaaa"[n] == '?';
}

// REPEAT 2 - TIME: 4.290587 s
