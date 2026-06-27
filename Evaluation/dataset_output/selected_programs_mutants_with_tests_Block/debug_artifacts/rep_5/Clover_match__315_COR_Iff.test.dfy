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
expect |"aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"| == |"aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}", "aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"| ==> "aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"[n] == "aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"[n] || "aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"[n] == '?';
}
method {:test} Test13() {
expect |"\U{0002}aaaaaaaa\U{0006}aaaaaa\U{0012}\U{000C}aa"| == |"\0\U{0004}aaaaaaa\na\U{000E}aaaaa\U{0010}\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaaaaaaa\U{0006}aaaaaa\U{0012}\U{000C}aa", "\0\U{0004}aaaaaaa\na\U{000E}aaaaa\U{0010}\U{0008}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaaaaaaa\U{0006}aaaaaa\U{0012}\U{000C}aa"| ==> "\U{0002}aaaaaaaa\U{0006}aaaaaa\U{0012}\U{000C}aa"[n] == "\0\U{0004}aaaaaaa\na\U{000E}aaaaa\U{0010}\U{0008}a"[n] || "\0\U{0004}aaaaaaa\na\U{000E}aaaaa\U{0010}\U{0008}a"[n] == '?';
}
method {:test} Test14() {
expect |"\0aaaaaaaa\U{0006}aaaaa\na\U{0016}\U{0012}\U{001C}"| == |"\0\U{0002}aaaaa\U{0004}aa\U{000C}\U{0010}a\U{0018}a\U{000E}\U{0014}a\U{0008}\U{001A}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaa\U{0006}aaaaa\na\U{0016}\U{0012}\U{001C}", "\0\U{0002}aaaaa\U{0004}aa\U{000C}\U{0010}a\U{0018}a\U{000E}\U{0014}a\U{0008}\U{001A}");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaa\U{0006}aaaaa\na\U{0016}\U{0012}\U{001C}"| ==> "\0aaaaaaaa\U{0006}aaaaa\na\U{0016}\U{0012}\U{001C}"[n] == "\0\U{0002}aaaaa\U{0004}aa\U{000C}\U{0010}a\U{0018}a\U{000E}\U{0014}a\U{0008}\U{001A}"[n] || "\0\U{0002}aaaaa\U{0004}aa\U{000C}\U{0010}a\U{0018}a\U{000E}\U{0014}a\U{0008}\U{001A}"[n] == '?';
}

// REPEAT 5 - TIME: 10.6892975 s
