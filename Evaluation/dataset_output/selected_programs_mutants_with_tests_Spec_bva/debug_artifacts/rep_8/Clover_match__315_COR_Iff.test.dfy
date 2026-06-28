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

method {:test} Test32() {
expect |"\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"| == |"\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}", "\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"| ==> "\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"[n] == "\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"[n] || "\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"[n] == '?';
}
method {:test} Test33() {
expect |"aaaaaaa\U{0008}\U{0014}\U{0016}\U{000C}\U{0010}\0"| == |"aa\U{0004}aa\U{000E}\n\U{0012}aaa\U{0006}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\U{0008}\U{0014}\U{0016}\U{000C}\U{0010}\0", "aa\U{0004}aa\U{000E}\n\U{0012}aaa\U{0006}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\U{0008}\U{0014}\U{0016}\U{000C}\U{0010}\0"| ==> "aaaaaaa\U{0008}\U{0014}\U{0016}\U{000C}\U{0010}\0"[n] == "aa\U{0004}aa\U{000E}\n\U{0012}aaa\U{0006}\U{0002}"[n] || "aa\U{0004}aa\U{000E}\n\U{0012}aaa\U{0006}\U{0002}"[n] == '?';
}

// REPEAT 8 - TIME: 23.8325839 s
