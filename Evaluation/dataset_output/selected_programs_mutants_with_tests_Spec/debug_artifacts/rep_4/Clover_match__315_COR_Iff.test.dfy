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
expect |"\U{0001}a"| == |"?a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}a", "?a");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}a"| ==> "\U{0001}a"[n] == "?a"[n] || "?a"[n] == '?';
}
method {:test} Test7() {
expect |"\naaaa\0aaaa\U{0006}"| == |"\U{0008}aaaa\U{0002}aaa\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naaaa\0aaaa\U{0006}", "\U{0008}aaaa\U{0002}aaa\U{0004}a");
expect r0 <==> forall n :: 0 <= n < |"\naaaa\0aaaa\U{0006}"| ==> "\naaaa\0aaaa\U{0006}"[n] == "\U{0008}aaaa\U{0002}aaa\U{0004}a"[n] || "\U{0008}aaaa\U{0002}aaa\U{0004}a"[n] == '?';
}

// REPEAT 4 - TIME: 7.1907163 s
