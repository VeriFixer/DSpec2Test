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

method {:test} Test9() {
expect |"\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"| == |"\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n", "\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"| ==> "\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"[n] == "\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"[n] || "\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"[n] == '?';
}
method {:test} Test10() {
expect |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"| == |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa", "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa");
expect r0 <==> forall n :: 0 <= n < |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"| ==> "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"[n] == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"[n] || "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"[n] == '?';
}
method {:test} Test11() {
expect |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}", "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"[n] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"[n] || "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"[n] == '?';
}

// REPEAT 4 - TIME: 8.5798025 s
