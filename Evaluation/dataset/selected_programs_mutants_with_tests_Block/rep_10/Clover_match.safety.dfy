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

method {:test} Test27() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test28() {
expect |"aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test29() {
expect |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 10 - TIME: 20.935086 s
