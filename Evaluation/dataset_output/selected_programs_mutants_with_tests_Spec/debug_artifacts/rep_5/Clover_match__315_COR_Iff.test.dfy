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

method {:test} Test8() {
expect |"aaaaaa\U{0001}aa\U{0003}a\U{0005}aaaaaaaaaaaa\U{0007}"| == |"?aa?a??aa?a?aaaaaaaaaaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaa\U{0001}aa\U{0003}a\U{0005}aaaaaaaaaaaa\U{0007}", "?aa?a??aa?a?aaaaaaaaaaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaa\U{0001}aa\U{0003}a\U{0005}aaaaaaaaaaaa\U{0007}"| ==> "aaaaaa\U{0001}aa\U{0003}a\U{0005}aaaaaaaaaaaa\U{0007}"[n] == "?aa?a??aa?a?aaaaaaaaaaaa?"[n] || "?aa?a??aa?a?aaaaaaaaaaaa?"[n] == '?';
}
method {:test} Test9() {
expect |"a\U{0004}\0"| == |"a\U{0006}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0004}\0", "a\U{0006}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0004}\0"| ==> "a\U{0004}\0"[n] == "a\U{0006}\U{0002}"[n] || "a\U{0006}\U{0002}"[n] == '?';
}

// REPEAT 5 - TIME: 9.0578891 s
