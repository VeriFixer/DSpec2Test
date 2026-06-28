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

method {:test} Test24() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaa\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaa\0"[n] || "aaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaaaaaaaaaa\0aaaaaaaaaaa"| == |"aaaaaaaaaaaaa\U{0002}aaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\0aaaaaaaaaaa", "aaaaaaaaaaaaa\U{0002}aaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\0aaaaaaaaaaa"| ==> "aaaaaaaaaaaaa\0aaaaaaaaaaa"[n] == "aaaaaaaaaaaaa\U{0002}aaaaaaaaaaa"[n] || "aaaaaaaaaaaaa\U{0002}aaaaaaaaaaa"[n] == '?';
}
method {:test} Test26() {
expect |"aaaaaaaaaa\0aaaaaaa\U{0006}aaaaaa"| == |"aaaaaaaaaa\0\U{0002}aaaaaa\U{0004}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaa\0aaaaaaa\U{0006}aaaaaa", "aaaaaaaaaa\0\U{0002}aaaaaa\U{0004}aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaa\0aaaaaaa\U{0006}aaaaaa"| ==> "aaaaaaaaaa\0aaaaaaa\U{0006}aaaaaa"[n] == "aaaaaaaaaa\0\U{0002}aaaaaa\U{0004}aaaaaa"[n] || "aaaaaaaaaa\0\U{0002}aaaaaa\U{0004}aaaaaa"[n] == '?';
}

// REPEAT 9 - TIME: 15.4472775 s
