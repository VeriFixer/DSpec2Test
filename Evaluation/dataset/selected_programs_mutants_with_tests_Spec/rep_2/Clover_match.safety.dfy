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

method {:test} Test2() {
expect |"\U{0001}"| == |"?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}", "?");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}"| ==> "\U{0001}"[n] == "?"[n] || "?"[n] == '?';
}
method {:test} Test3() {
expect |"\0"| == |"\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0", "\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\0"| ==> "\0"[n] == "\U{0002}"[n] || "\U{0002}"[n] == '?';
}

// REPEAT 2 - TIME: 4.1672417 s
