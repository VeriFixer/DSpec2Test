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

method {:test} Test18() {
expect |"\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"| == |"\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n", "\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"| ==> "\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"[n] == "\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"[n] || "\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"[n] == '?';
}
method {:test} Test19() {
expect |"\U{0016}aaaaaaaaaaaa\0\U{0006}aaaaa\U{0008}a\naa"| == |"\U{0014}aaaa\U{000E}aa\U{0004}aa\U{0010}a\U{0002}aaaa\U{000C}aa\U{0012}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0016}aaaaaaaaaaaa\0\U{0006}aaaaa\U{0008}a\naa", "\U{0014}aaaa\U{000E}aa\U{0004}aa\U{0010}a\U{0002}aaaa\U{000C}aa\U{0012}aaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0016}aaaaaaaaaaaa\0\U{0006}aaaaa\U{0008}a\naa"| ==> "\U{0016}aaaaaaaaaaaa\0\U{0006}aaaaa\U{0008}a\naa"[n] == "\U{0014}aaaa\U{000E}aa\U{0004}aa\U{0010}a\U{0002}aaaa\U{000C}aa\U{0012}aaa"[n] || "\U{0014}aaaa\U{000E}aa\U{0004}aa\U{0010}a\U{0002}aaaa\U{000C}aa\U{0012}aaa"[n] == '?';
}

// REPEAT 10 - TIME: 12.4441612 s
