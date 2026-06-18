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

method {:test} Test14() {
expect |"\U{0006}a\0a\U{0002}\U{0004}"| == |"\U{0006}a\0a\U{0002}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}a\0a\U{0002}\U{0004}", "\U{0006}a\0a\U{0002}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}a\0a\U{0002}\U{0004}"| ==> "\U{0006}a\0a\U{0002}\U{0004}"[n] == "\U{0006}a\0a\U{0002}\U{0004}"[n] || "\U{0006}a\0a\U{0002}\U{0004}"[n] == '?';
}
method {:test} Test15() {
expect |"\U{0012}a\0aaaaaaa\U{0010}\n"| == |"\U{0006}a\U{0002}aa\U{000C}\U{0004}aa\U{0008}a\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0012}a\0aaaaaaa\U{0010}\n", "\U{0006}a\U{0002}aa\U{000C}\U{0004}aa\U{0008}a\U{000E}");
expect r0 <==> forall n :: 0 <= n < |"\U{0012}a\0aaaaaaa\U{0010}\n"| ==> "\U{0012}a\0aaaaaaa\U{0010}\n"[n] == "\U{0006}a\U{0002}aa\U{000C}\U{0004}aa\U{0008}a\U{000E}"[n] || "\U{0006}a\U{0002}aa\U{000C}\U{0004}aa\U{0008}a\U{000E}"[n] == '?';
}

// REPEAT 8 - TIME: 12.5807697 s
