method {:testEntry} Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall n :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
  {
    if s[i] != p[i] && p[i] != '?'
    {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method {:test} Test6() {
expect |"\U{0002}\0"| == |"\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0", "\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0"| ==> "\U{0002}\0"[n] == "\U{0002}\0"[n] || "\U{0002}\0"[n] == '?';
}
method {:test} Test7() {
expect |"\U{0006}\U{0002}"| == |"\U{0004}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}\U{0002}", "\U{0004}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}\U{0002}"| ==> "\U{0006}\U{0002}"[n] == "\U{0004}\0"[n] || "\U{0004}\0"[n] == '?';
}

// REPEAT 4 - TIME: 6.7280595 s
