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

method {:test} Test26() {
expect |"\U{0006}aa\U{0004}\U{0002}\0"| == |"\U{0006}aa\U{0004}\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}aa\U{0004}\U{0002}\0", "\U{0006}aa\U{0004}\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}aa\U{0004}\U{0002}\0"| ==> "\U{0006}aa\U{0004}\U{0002}\0"[n] == "\U{0006}aa\U{0004}\U{0002}\0"[n] || "\U{0006}aa\U{0004}\U{0002}\0"[n] == '?';
}
method {:test} Test27() {
expect |"\U{0006}aaaa\0a\U{0008}\U{0012}\U{000E}"| == |"a\U{0004}\U{0002}aa\n\U{000C}\U{0010}\U{0014}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}aaaa\0a\U{0008}\U{0012}\U{000E}", "a\U{0004}\U{0002}aa\n\U{000C}\U{0010}\U{0014}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}aaaa\0a\U{0008}\U{0012}\U{000E}"| ==> "\U{0006}aaaa\0a\U{0008}\U{0012}\U{000E}"[n] == "a\U{0004}\U{0002}aa\n\U{000C}\U{0010}\U{0014}a"[n] || "a\U{0004}\U{0002}aa\n\U{000C}\U{0010}\U{0014}a"[n] == '?';
}

// REPEAT 5 - TIME: 20.0711421 s
