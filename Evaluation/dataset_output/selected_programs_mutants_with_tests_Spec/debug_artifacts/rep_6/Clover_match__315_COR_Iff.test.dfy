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

method {:test} Test10() {
expect |"\0aaaaaaa"| == |"?a?aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaa", "?a?aaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaa"| ==> "\0aaaaaaa"[n] == "?a?aaaaa"[n] || "?a?aaaaa"[n] == '?';
}
method {:test} Test11() {
expect |"\na\U{0006}aa\U{000E}aa\0\U{0012}"| == |"\U{0014}a\U{0004}\U{000C}a\U{0010}aa\U{0002}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\na\U{0006}aa\U{000E}aa\0\U{0012}", "\U{0014}a\U{0004}\U{000C}a\U{0010}aa\U{0002}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\na\U{0006}aa\U{000E}aa\0\U{0012}"| ==> "\na\U{0006}aa\U{000E}aa\0\U{0012}"[n] == "\U{0014}a\U{0004}\U{000C}a\U{0010}aa\U{0002}\U{0008}"[n] || "\U{0014}a\U{0004}\U{000C}a\U{0010}aa\U{0002}\U{0008}"[n] == '?';
}

// REPEAT 6 - TIME: 10.6150492 s
