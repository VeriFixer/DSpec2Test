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

method {:test} Test24() {
expect |"aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"| == |"aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n", "aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"| ==> "aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"[n] == "aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"[n] || "aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{000E}"| == |"aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}aaaaa\0\n\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{000E}", "aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}aaaaa\0\n\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{000E}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{000E}"[n] == "aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}aaaaa\0\n\U{000C}"[n] || "aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}aaaaa\0\n\U{000C}"[n] == '?';
}

// REPEAT 4 - TIME: 12.9938737 s
