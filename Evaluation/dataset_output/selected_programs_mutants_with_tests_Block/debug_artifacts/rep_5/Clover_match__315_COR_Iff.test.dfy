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

method {:test} Test12() {
expect |"\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"| == |"\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n", "\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"| ==> "\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"[n] == "\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"[n] || "\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"[n] == '?';
}
method {:test} Test13() {
expect |"\U{0004}aaaa\U{0002}aaaaa"| == |"\U{0004}aaaa\0aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaa\U{0002}aaaaa", "\U{0004}aaaa\0aaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaa\U{0002}aaaaa"| ==> "\U{0004}aaaa\U{0002}aaaaa"[n] == "\U{0004}aaaa\0aaaaa"[n] || "\U{0004}aaaa\0aaaaa"[n] == '?';
}
method {:test} Test14() {
expect |"\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"| == |"\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}", "\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}");
expect r0 <==> forall n :: 0 <= n < |"\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"| ==> "\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"[n] == "\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"[n] || "\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"[n] == '?';
}

// REPEAT 5 - TIME: 9.0560942 s
