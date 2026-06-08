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

method {:test} Test34() {
expect |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"| == |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a", "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"| ==> "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"[n] == "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"[n] || "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"[n] == '?';
}
method {:test} Test35() {
expect |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}"| == |"aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}", "aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}"| ==> "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}"[n] == "aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a"[n] || "aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a"[n] == '?';
}

// REPEAT 9 - TIME: 20.6744833 s
