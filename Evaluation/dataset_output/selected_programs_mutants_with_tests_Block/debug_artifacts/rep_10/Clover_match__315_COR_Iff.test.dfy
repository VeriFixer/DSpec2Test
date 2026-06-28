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

method {:test} Test27() {
expect |"aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"| == |"aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}", "aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"| ==> "aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"[n] == "aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"[n] || "aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"[n] == '?';
}
method {:test} Test28() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaa"| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaaaaaaaaaaaaaaaaa"| ==> "\0aaaaaaaaaaaaaaaaaaaaaaa"[n] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa"[n] || "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test29() {
expect |"aaaaaaaaaaaaaaaaaaaaaa\0a"| == |"aaaaaaaaaaaaaaaaaaaaaa\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaa\0a", "aaaaaaaaaaaaaaaaaaaaaa\0a");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaa\0a"| ==> "aaaaaaaaaaaaaaaaaaaaaa\0a"[n] == "aaaaaaaaaaaaaaaaaaaaaa\0a"[n] || "aaaaaaaaaaaaaaaaaaaaaa\0a"[n] == '?';
}

// REPEAT 10 - TIME: 17.331566 s
