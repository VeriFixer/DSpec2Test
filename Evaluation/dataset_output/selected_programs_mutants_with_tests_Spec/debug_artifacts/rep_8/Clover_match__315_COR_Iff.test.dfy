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

method {:test} Test14() {
expect |"aaaaaaa\0aaaaaaaa\U{0004}aaaaaaaaa\U{0002}"| == |"aaaaaaa?aaa?a?aa?a?aaaaaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\0aaaaaaaa\U{0004}aaaaaaaaa\U{0002}", "aaaaaaa?aaa?a?aa?a?aaaaaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\0aaaaaaaa\U{0004}aaaaaaaaa\U{0002}"| ==> "aaaaaaa\0aaaaaaaa\U{0004}aaaaaaaaa\U{0002}"[n] == "aaaaaaa?aaa?a?aa?a?aaaaaaa?"[n] || "aaaaaaa?aaa?a?aa?a?aaaaaaa?"[n] == '?';
}
method {:test} Test15() {
expect |"aaaaaaaaaaaaa\U{000C}aa\U{0008}aaaaaaa\0a\U{0010}a\U{0014}"| == |"aa\U{0004}aaaaaaaa\U{000E}aaaa\U{0006}aaaaaa\n\U{0002}\U{0012}\U{0018}a\U{0016}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\U{000C}aa\U{0008}aaaaaaa\0a\U{0010}a\U{0014}", "aa\U{0004}aaaaaaaa\U{000E}aaaa\U{0006}aaaaaa\n\U{0002}\U{0012}\U{0018}a\U{0016}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\U{000C}aa\U{0008}aaaaaaa\0a\U{0010}a\U{0014}"| ==> "aaaaaaaaaaaaa\U{000C}aa\U{0008}aaaaaaa\0a\U{0010}a\U{0014}"[n] == "aa\U{0004}aaaaaaaa\U{000E}aaaa\U{0006}aaaaaa\n\U{0002}\U{0012}\U{0018}a\U{0016}"[n] || "aa\U{0004}aaaaaaaa\U{000E}aaaa\U{0006}aaaaaa\n\U{0002}\U{0012}\U{0018}a\U{0016}"[n] == '?';
}

// REPEAT 8 - TIME: 13.3953457 s
