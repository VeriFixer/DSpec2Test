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

method {:test} Test28() {
expect |"aaaaaaa\U{0002}a\U{0004}\0"| == |"aaaaaaa\U{0002}a\U{0004}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\U{0002}a\U{0004}\0", "aaaaaaa\U{0002}a\U{0004}\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\U{0002}a\U{0004}\0"| ==> "aaaaaaa\U{0002}a\U{0004}\0"[n] == "aaaaaaa\U{0002}a\U{0004}\0"[n] || "aaaaaaa\U{0002}a\U{0004}\0"[n] == '?';
}
method {:test} Test29() {
expect |"aaa\U{0004}\n\U{000C}aaa\U{0012}\U{000E}"| == |"aa\U{0002}aa\0\U{0008}\U{0010}aa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{0004}\n\U{000C}aaa\U{0012}\U{000E}", "aa\U{0002}aa\0\U{0008}\U{0010}aa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{0004}\n\U{000C}aaa\U{0012}\U{000E}"| ==> "aaa\U{0004}\n\U{000C}aaa\U{0012}\U{000E}"[n] == "aa\U{0002}aa\0\U{0008}\U{0010}aa\U{0006}"[n] || "aa\U{0002}aa\0\U{0008}\U{0010}aa\U{0006}"[n] == '?';
}

// REPEAT 6 - TIME: 21.2803447 s
