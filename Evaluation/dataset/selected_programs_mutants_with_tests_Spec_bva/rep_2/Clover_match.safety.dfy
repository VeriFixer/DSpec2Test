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

method {:test} Test20() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| == |"?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}", "?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[n] == "?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?"[n] || "?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?"[n] == '?';
}
method {:test} Test21() {
expect |"\U{0008}\U{0004}\0"| == |"\n\U{0002}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}\U{0004}\0", "\n\U{0002}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}\U{0004}\0"| ==> "\U{0008}\U{0004}\0"[n] == "\n\U{0002}\U{0006}"[n] || "\n\U{0002}\U{0006}"[n] == '?';
}

// REPEAT 2 - TIME: 11.1987083 s
