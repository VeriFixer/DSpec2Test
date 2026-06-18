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

method {:test} Test3() {
expect |"aa\U{0005}aaaaaaaa\0\U{0002}"| == |"a?\U{0005}aaaaaaaa\0\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\U{0005}aaaaaaaa\0\U{0002}", "a?\U{0005}aaaaaaaa\0\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aa\U{0005}aaaaaaaa\0\U{0002}"| ==> "aa\U{0005}aaaaaaaa\0\U{0002}"[n] == "a?\U{0005}aaaaaaaa\0\U{0002}"[n] || "a?\U{0005}aaaaaaaa\0\U{0002}"[n] == '?';
}
method {:test} Test4() {
expect |"a\U{0008}\U{0002}aaaaa\U{0004}"| == |"a\0aaaaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0008}\U{0002}aaaaa\U{0004}", "a\0aaaaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0008}\U{0002}aaaaa\U{0004}"| ==> "a\U{0008}\U{0002}aaaaa\U{0004}"[n] == "a\0aaaaaa\U{0006}"[n] || "a\0aaaaaa\U{0006}"[n] == '?';
}
method {:test} Test5() {
expect |"\U{0006}a\0aaaaaaa\U{0002}"| == |"\U{0006}\U{0008}aaaaaaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}a\0aaaaaaa\U{0002}", "\U{0006}\U{0008}aaaaaaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}a\0aaaaaaa\U{0002}"| ==> "\U{0006}a\0aaaaaaa\U{0002}"[n] == "\U{0006}\U{0008}aaaaaaaa\U{0004}"[n] || "\U{0006}\U{0008}aaaaaaaa\U{0004}"[n] == '?';
}

// REPEAT 2 - TIME: 4.7700315 s
