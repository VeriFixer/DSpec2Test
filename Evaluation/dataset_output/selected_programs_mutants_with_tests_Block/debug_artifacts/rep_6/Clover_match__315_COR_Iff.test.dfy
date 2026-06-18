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

method {:test} Test15() {
expect |"aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"| == |"aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa", "aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"| ==> "aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"[n] == "aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"[n] || "aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"[n] == '?';
}
method {:test} Test16() {
expect |"\0aa"| == |"\U{0002}a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa", "\U{0002}a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\0aa"| ==> "\0aa"[n] == "\U{0002}a\U{0004}"[n] || "\U{0002}a\U{0004}"[n] == '?';
}
method {:test} Test17() {
expect |"aaaaaa\0aaaaaa\U{0002}aaaaa\U{0008}aaa\U{000C}"| == |"aaaaaa\0aa\U{0006}aaaa\U{0004}aaaaaaaa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaa\0aaaaaa\U{0002}aaaaa\U{0008}aaa\U{000C}", "aaaaaa\0aa\U{0006}aaaa\U{0004}aaaaaaaa\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaa\0aaaaaa\U{0002}aaaaa\U{0008}aaa\U{000C}"| ==> "aaaaaa\0aaaaaa\U{0002}aaaaa\U{0008}aaa\U{000C}"[n] == "aaaaaa\0aa\U{0006}aaaa\U{0004}aaaaaaaa\n"[n] || "aaaaaa\0aa\U{0006}aaaa\U{0004}aaaaaaaa\n"[n] == '?';
}

// REPEAT 6 - TIME: 11.0793623 s
