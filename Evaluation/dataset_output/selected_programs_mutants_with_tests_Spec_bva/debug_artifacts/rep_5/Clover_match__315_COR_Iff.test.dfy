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

method {:test} Test26() {
expect |"\U{0004}aa\0aaa\U{0002}aa"| == |"\U{0004}aa\0aaa\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aa\0aaa\U{0002}aa", "\U{0004}aa\0aaa\U{0002}aa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aa\0aaa\U{0002}aa"| ==> "\U{0004}aa\0aaa\U{0002}aa"[n] == "\U{0004}aa\0aaa\U{0002}aa"[n] || "\U{0004}aa\0aaa\U{0002}aa"[n] == '?';
}
method {:test} Test27() {
expect |"\U{0008}a\U{0004}a"| == |"\U{0006}a\0\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}a\U{0004}a", "\U{0006}a\0\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}a\U{0004}a"| ==> "\U{0008}a\U{0004}a"[n] == "\U{0006}a\0\U{0002}"[n] || "\U{0006}a\0\U{0002}"[n] == '?';
}

// REPEAT 5 - TIME: 17.7815492 s
