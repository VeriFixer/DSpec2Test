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
expect |"\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"| == |"\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}", "\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"| ==> "\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"[n] == "\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"[n] || "\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"[n] == '?';
}
method {:test} Test13() {
expect |"aaaaaaaaaaaa\0aa\U{0010}aaaaaaa\U{000C}a\U{0012}"| == |"aaaaaaaaaaa\U{0008}\U{0002}aa\n\U{000E}aa\U{0004}aaa\U{0006}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaa\0aa\U{0010}aaaaaaa\U{000C}a\U{0012}", "aaaaaaaaaaa\U{0008}\U{0002}aa\n\U{000E}aa\U{0004}aaa\U{0006}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaa\0aa\U{0010}aaaaaaa\U{000C}a\U{0012}"| ==> "aaaaaaaaaaaa\0aa\U{0010}aaaaaaa\U{000C}a\U{0012}"[n] == "aaaaaaaaaaa\U{0008}\U{0002}aa\n\U{000E}aa\U{0004}aaa\U{0006}aa"[n] || "aaaaaaaaaaa\U{0008}\U{0002}aa\n\U{000E}aa\U{0004}aaa\U{0006}aa"[n] == '?';
}

// REPEAT 7 - TIME: 12.0677475 s
