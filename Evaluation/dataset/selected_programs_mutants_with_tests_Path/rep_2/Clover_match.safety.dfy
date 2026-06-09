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

method {:test} Test3() {
expect |"aa"| == |"aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa", "aa");
expect r0 <==> forall n :: 0 <= n < |"aa"| ==> "aa"[n] == "aa"[n] || "aa"[n] == '?';
}
method {:test} Test4() {
expect |"\U{0004}\U{0002}"| == |"\U{0006}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\U{0002}", "\U{0006}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\U{0002}"| ==> "\U{0004}\U{0002}"[n] == "\U{0006}\0"[n] || "\U{0006}\0"[n] == '?';
}

// REPEAT 2 - TIME: 43.166029 s
