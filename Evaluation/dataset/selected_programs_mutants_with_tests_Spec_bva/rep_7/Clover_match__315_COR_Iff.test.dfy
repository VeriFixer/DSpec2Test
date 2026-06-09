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

method {:test} Test30() {
expect |"\0aaaa\U{0002}"| == |"?a????"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaa\U{0002}", "?a????");
expect r0 <==> forall n :: 0 <= n < |"\0aaaa\U{0002}"| ==> "\0aaaa\U{0002}"[n] == "?a????"[n] || "?a????"[n] == '?';
}
method {:test} Test31() {
expect |"aaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaa\0\U{000C}aaaa"| == |"aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}\U{0002}aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaa\0\U{000C}aaaa", "aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}\U{0002}aaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaa\0\U{000C}aaaa"| ==> "aaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaa\0\U{000C}aaaa"[n] == "aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}\U{0002}aaaaa"[n] || "aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}\U{0002}aaaaa"[n] == '?';
}

// REPEAT 7 - TIME: 15.9203579 s
