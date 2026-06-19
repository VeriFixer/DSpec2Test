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
expect |"aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"| == |"aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n", "aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"| ==> "aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"[n] == "aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"[n] || "aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"[n] == '?';
}
method {:test} Test25() {
expect |"aaa\U{0002}aaaaaaaaaa\U{0008}aaaa\U{000C}"| == |"aaa\0aaaaaaa\U{0004}a\U{0006}aaaaa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{0002}aaaaaaaaaa\U{0008}aaaa\U{000C}", "aaa\0aaaaaaa\U{0004}a\U{0006}aaaaa\n");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{0002}aaaaaaaaaa\U{0008}aaaa\U{000C}"| ==> "aaa\U{0002}aaaaaaaaaa\U{0008}aaaa\U{000C}"[n] == "aaa\0aaaaaaa\U{0004}a\U{0006}aaaaa\n"[n] || "aaa\0aaaaaaa\U{0004}a\U{0006}aaaaa\n"[n] == '?';
}
method {:test} Test26() {
expect |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| == |"\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aa\0aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aa\0aaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| ==> "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[n] == "\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aa\0aaaaa"[n] || "\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aa\0aaaaa"[n] == '?';
}

// REPEAT 9 - TIME: 828.1418782 s
