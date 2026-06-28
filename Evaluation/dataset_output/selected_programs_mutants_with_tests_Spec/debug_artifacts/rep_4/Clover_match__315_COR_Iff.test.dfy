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

method {:test} Test6() {
expect |"\U{0003}aaa\U{0001}"| == |"??aa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0003}aaa\U{0001}", "??aa?");
expect r0 <==> forall n :: 0 <= n < |"\U{0003}aaa\U{0001}"| ==> "\U{0003}aaa\U{0001}"[n] == "??aa?"[n] || "??aa?"[n] == '?';
}
method {:test} Test7() {
expect |"\n\0\U{0004}aaaaaaaa"| == |"\U{0008}\U{0002}\U{0006}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\n\0\U{0004}aaaaaaaa", "\U{0008}\U{0002}\U{0006}aaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\n\0\U{0004}aaaaaaaa"| ==> "\n\0\U{0004}aaaaaaaa"[n] == "\U{0008}\U{0002}\U{0006}aaaaaaaa"[n] || "\U{0008}\U{0002}\U{0006}aaaaaaaa"[n] == '?';
}

// REPEAT 4 - TIME: 7.7885366 s
