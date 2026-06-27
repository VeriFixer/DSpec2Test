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
expect |"\U{0004}aa\U{0006}aaa\U{0002}a\0"| == |"\U{0004}aa\U{0006}aaa\U{0002}a\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aa\U{0006}aaa\U{0002}a\0", "\U{0004}aa\U{0006}aaa\U{0002}a\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aa\U{0006}aaa\U{0002}a\0"| ==> "\U{0004}aa\U{0006}aaa\U{0002}a\0"[n] == "\U{0004}aa\U{0006}aaa\U{0002}a\0"[n] || "\U{0004}aa\U{0006}aaa\U{0002}a\0"[n] == '?';
}
method {:test} Test10() {
expect |"a\U{0008}a\U{0004}"| == |"a\0\U{0002}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0008}a\U{0004}", "a\0\U{0002}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0008}a\U{0004}"| ==> "a\U{0008}a\U{0004}"[n] == "a\0\U{0002}\U{0006}"[n] || "a\0\U{0002}\U{0006}"[n] == '?';
}
method {:test} Test11() {
expect |"\U{0008}aa\U{0002}"| == |"\U{0006}\0a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}aa\U{0002}", "\U{0006}\0a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}aa\U{0002}"| ==> "\U{0008}aa\U{0002}"[n] == "\U{0006}\0a\U{0004}"[n] || "\U{0006}\0a\U{0004}"[n] == '?';
}

// REPEAT 4 - TIME: 136.1439813 s
