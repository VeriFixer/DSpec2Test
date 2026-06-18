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
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"[n] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"[n] || "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"[n] == '?';
}
method {:test} Test28() {
expect |"\U{0004}a\U{0002}aaaaaaaaaaaaaaa"| == |"\U{0004}a\0aaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}a\U{0002}aaaaaaaaaaaaaaa", "\U{0004}a\0aaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}a\U{0002}aaaaaaaaaaaaaaa"| ==> "\U{0004}a\U{0002}aaaaaaaaaaaaaaa"[n] == "\U{0004}a\0aaaaaaaaaaaaaaa"[n] || "\U{0004}a\0aaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test29() {
expect |"\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"| == |"\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0", "\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"| ==> "\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"[n] == "\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"[n] || "\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"[n] == '?';
}

// REPEAT 10 - TIME: 17.3889335 s
