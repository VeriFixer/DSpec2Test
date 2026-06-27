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
expect |"aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"| == |"aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}", "aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"| ==> "aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"[n] == "aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"[n] || "aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"[n] == '?';
}
method {:test} Test16() {
expect |"aaaaaaaaaaaaaaaa\U{0006}a\0\U{0008}aaaaaaa\U{0004}"| == |"aaaaaaaaaaaaaaaa\U{0006}a\U{0002}\U{0008}aaaaaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaa\U{0006}a\0\U{0008}aaaaaaa\U{0004}", "aaaaaaaaaaaaaaaa\U{0006}a\U{0002}\U{0008}aaaaaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaa\U{0006}a\0\U{0008}aaaaaaa\U{0004}"| ==> "aaaaaaaaaaaaaaaa\U{0006}a\0\U{0008}aaaaaaa\U{0004}"[n] == "aaaaaaaaaaaaaaaa\U{0006}a\U{0002}\U{0008}aaaaaaa\U{0004}"[n] || "aaaaaaaaaaaaaaaa\U{0006}a\U{0002}\U{0008}aaaaaaa\U{0004}"[n] == '?';
}
method {:test} Test17() {
expect |"aaaaaaaaaaaaa\0aaaa\U{0004}"| == |"aaaaaaaaaaaaa\U{0002}aaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\0aaaa\U{0004}", "aaaaaaaaaaaaa\U{0002}aaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\0aaaa\U{0004}"| ==> "aaaaaaaaaaaaa\0aaaa\U{0004}"[n] == "aaaaaaaaaaaaa\U{0002}aaaa\U{0004}"[n] || "aaaaaaaaaaaaa\U{0002}aaaa\U{0004}"[n] == '?';
}

// REPEAT 6 - TIME: 268.8425911 s
