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

method {:test} Test9() {
expect |"aaaaaaa\0a\U{0004}\U{0002}\U{0006}"| == |"aaaaaaa\0a\U{0004}\U{0002}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\0a\U{0004}\U{0002}\U{0006}", "aaaaaaa\0a\U{0004}\U{0002}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\0a\U{0004}\U{0002}\U{0006}"| ==> "aaaaaaa\0a\U{0004}\U{0002}\U{0006}"[n] == "aaaaaaa\0a\U{0004}\U{0002}\U{0006}"[n] || "aaaaaaa\0a\U{0004}\U{0002}\U{0006}"[n] == '?';
}
method {:test} Test10() {
expect |"a\0\U{0006}aa\U{0004}\U{0002}"| == |"a\0\U{0008}aa\U{0004}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0\U{0006}aa\U{0004}\U{0002}", "a\0\U{0008}aa\U{0004}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"a\0\U{0006}aa\U{0004}\U{0002}"| ==> "a\0\U{0006}aa\U{0004}\U{0002}"[n] == "a\0\U{0008}aa\U{0004}\U{0002}"[n] || "a\0\U{0008}aa\U{0004}\U{0002}"[n] == '?';
}
method {:test} Test11() {
expect |"aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"| == |"aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n", "aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"| ==> "aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"[n] == "aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"[n] || "aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"[n] == '?';
}

// REPEAT 4 - TIME: 8.3685015 s
