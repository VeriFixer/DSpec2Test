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
expect |"\0aaa\U{0002}"| == |"\0aaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaa\U{0002}", "\0aaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\0aaa\U{0002}"| ==> "\0aaa\U{0002}"[n] == "\0aaa\U{0002}"[n] || "\0aaa\U{0002}"[n] == '?';
}
method {:test} Test25() {
expect |"aaa\U{0006}a\n\0\U{000C}"| == |"\U{0002}aa\U{0004}aa\U{0008}\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{0006}a\n\0\U{000C}", "\U{0002}aa\U{0004}aa\U{0008}\U{000E}");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{0006}a\n\0\U{000C}"| ==> "aaa\U{0006}a\n\0\U{000C}"[n] == "\U{0002}aa\U{0004}aa\U{0008}\U{000E}"[n] || "\U{0002}aa\U{0004}aa\U{0008}\U{000E}"[n] == '?';
}

// REPEAT 4 - TIME: 16.4651013 s
