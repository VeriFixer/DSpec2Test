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
expect |"\U{0004}\U{0002}\0"| == |"\U{0004}\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\U{0002}\0", "\U{0004}\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\U{0002}\0"| ==> "\U{0004}\U{0002}\0"[n] == "\U{0004}\U{0002}\0"[n] || "\U{0004}\U{0002}\0"[n] == '?';
}
method {:test} Test9() {
expect |"\U{000C}aaaa\0aaa\U{0006}\n"| == |"\U{0004}aaaa\U{0002}aaa\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{000C}aaaa\0aaa\U{0006}\n", "\U{0004}aaaa\U{0002}aaa\U{0008}a");
expect r0 <==> forall n :: 0 <= n < |"\U{000C}aaaa\0aaa\U{0006}\n"| ==> "\U{000C}aaaa\0aaa\U{0006}\n"[n] == "\U{0004}aaaa\U{0002}aaa\U{0008}a"[n] || "\U{0004}aaaa\U{0002}aaa\U{0008}a"[n] == '?';
}

// REPEAT 5 - TIME: 8.4505857 s
