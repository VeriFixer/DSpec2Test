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
expect |"\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"| == |"\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}", "\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"| ==> "\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"[n] == "\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"[n] || "\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"[n] == '?';
}
method {:test} Test19() {
expect |"aaaaaaaaaaaaaaaaaaa\0aaaa\U{0008}aaaa"| == |"aaaaaaaaaaaaaaaaaaa\na\U{0002}a\U{0004}aaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaa\0aaaa\U{0008}aaaa", "aaaaaaaaaaaaaaaaaaa\na\U{0002}a\U{0004}aaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaa\0aaaa\U{0008}aaaa"| ==> "aaaaaaaaaaaaaaaaaaa\0aaaa\U{0008}aaaa"[n] == "aaaaaaaaaaaaaaaaaaa\na\U{0002}a\U{0004}aaaa\U{0006}"[n] || "aaaaaaaaaaaaaaaaaaa\na\U{0002}a\U{0004}aaaa\U{0006}"[n] == '?';
}
method {:test} Test20() {
expect |"aaaaaaaaaaaa\0aaaaaaaaaaa\U{0006}"| == |"aaaaaaaaaaaa\0aaaaaaaaa\U{0002}\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaa\0aaaaaaaaaaa\U{0006}", "aaaaaaaaaaaa\0aaaaaaaaa\U{0002}\U{0004}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaa\0aaaaaaaaaaa\U{0006}"| ==> "aaaaaaaaaaaa\0aaaaaaaaaaa\U{0006}"[n] == "aaaaaaaaaaaa\0aaaaaaaaa\U{0002}\U{0004}a"[n] || "aaaaaaaaaaaa\0aaaaaaaaa\U{0002}\U{0004}a"[n] == '?';
}

// REPEAT 7 - TIME: 15.1390965 s
