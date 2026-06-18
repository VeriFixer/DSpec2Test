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

method {:test} Test30() {
expect |"aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"| == |"aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}", "aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"| ==> "aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"[n] == "aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"[n] || "aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"[n] == '?';
}
method {:test} Test31() {
expect |"aaaaaaa\U{0012}\0\U{000C}aaaaaaaaa\U{0006}\U{0010}aaaaaaaa\U{0016}"| == |"aaa\na\U{000E}\U{0008}a\U{0002}aaaaaaaaaaaaaaa\U{0004}aaaa\U{0014}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\U{0012}\0\U{000C}aaaaaaaaa\U{0006}\U{0010}aaaaaaaa\U{0016}", "aaa\na\U{000E}\U{0008}a\U{0002}aaaaaaaaaaaaaaa\U{0004}aaaa\U{0014}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\U{0012}\0\U{000C}aaaaaaaaa\U{0006}\U{0010}aaaaaaaa\U{0016}"| ==> "aaaaaaa\U{0012}\0\U{000C}aaaaaaaaa\U{0006}\U{0010}aaaaaaaa\U{0016}"[n] == "aaa\na\U{000E}\U{0008}a\U{0002}aaaaaaaaaaaaaaa\U{0004}aaaa\U{0014}"[n] || "aaa\na\U{000E}\U{0008}a\U{0002}aaaaaaaaaaaaaaa\U{0004}aaaa\U{0014}"[n] == '?';
}

// REPEAT 7 - TIME: 17.3162826 s
