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
expect |"aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"| == |"aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}", "aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"| ==> "aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"[n] == "aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"[n] || "aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"[n] == '?';
}
method {:test} Test19() {
expect |"\U{0004}aaaa\0a"| == |"\U{0002}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaa\0a", "\U{0002}aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaa\0a"| ==> "\U{0004}aaaa\0a"[n] == "\U{0002}aaaaaa"[n] || "\U{0002}aaaaaa"[n] == '?';
}

// REPEAT 7 - TIME: 348.7564799 s
