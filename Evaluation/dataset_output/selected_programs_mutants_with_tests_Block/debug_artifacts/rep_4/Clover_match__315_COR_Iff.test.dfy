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
expect |"a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"| == |"a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}", "a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"| ==> "a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"[n] == "a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"[n] || "a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"[n] == '?';
}
method {:test} Test10() {
expect |"\n\0aaa\U{0002}aaa\U{0004}\U{0006}"| == |"\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\n\0aaa\U{0002}aaa\U{0004}\U{0006}", "\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\n\0aaa\U{0002}aaa\U{0004}\U{0006}"| ==> "\n\0aaa\U{0002}aaa\U{0004}\U{0006}"[n] == "\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"[n] || "\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"[n] == '?';
}
method {:test} Test11() {
expect |"\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"| == |"\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na", "\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na");
expect r0 <==> forall n :: 0 <= n < |"\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"| ==> "\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"[n] == "\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"[n] || "\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"[n] == '?';
}

// REPEAT 4 - TIME: 7.8522038 s
