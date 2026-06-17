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
expect |"\U{0007}aaaaaaaaaa\U{0005}\U{0001}aaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaa\taaaa"| == |"?aaaaaaaaaa??aa?aaaaaa?aaaaaaaa?aaaaaa????aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0007}aaaaaaaaaa\U{0005}\U{0001}aaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaa\taaaa", "?aaaaaaaaaa??aa?aaaaaa?aaaaaaaa?aaaaaa????aaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0007}aaaaaaaaaa\U{0005}\U{0001}aaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaa\taaaa"| ==> "\U{0007}aaaaaaaaaa\U{0005}\U{0001}aaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaa\taaaa"[n] == "?aaaaaaaaaa??aa?aaaaaa?aaaaaaaa?aaaaaa????aaa"[n] || "?aaaaaaaaaa??aa?aaaaaa?aaaaaaaa?aaaaaa????aaa"[n] == '?';
}
method {:test} Test19() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}aaa\U{0006}aaaaaaaaaaaaaa\U{0010}"| == |"aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaa\U{0002}aaaaaaaaaaaa\na\U{000C}\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}aaa\U{0006}aaaaaaaaaaaaaa\U{0010}", "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaa\U{0002}aaaaaaaaaaaa\na\U{000C}\U{000E}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}aaa\U{0006}aaaaaaaaaaaaaa\U{0010}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}aaa\U{0006}aaaaaaaaaaaaaa\U{0010}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaa\U{0002}aaaaaaaaaaaa\na\U{000C}\U{000E}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaa\U{0002}aaaaaaaaaaaa\na\U{000C}\U{000E}"[n] == '?';
}

// REPEAT 10 - TIME: 16.55676 s
