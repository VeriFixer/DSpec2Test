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
expect |"\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"| == |"\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n", "\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"| ==> "\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"[n] == "\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"[n] || "\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"[n] == '?';
}
method {:test} Test10() {
expect |"\0aaaaaaaa\U{0006}aaaaaaaa\U{0008}"| == |"\U{0002}aa\U{0004}aaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaa\U{0006}aaaaaaaa\U{0008}", "\U{0002}aa\U{0004}aaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaa\U{0006}aaaaaaaa\U{0008}"| ==> "\0aaaaaaaa\U{0006}aaaaaaaa\U{0008}"[n] == "\U{0002}aa\U{0004}aaaaaaaaaaaaaaa"[n] || "\U{0002}aa\U{0004}aaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test11() {
expect |"\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{000C}"| == |"\U{0002}\0a\naaa\U{0008}aaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{000C}", "\U{0002}\0a\naaa\U{0008}aaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{000C}"| ==> "\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{000C}"[n] == "\U{0002}\0a\naaa\U{0008}aaaaaaaaaaa"[n] || "\U{0002}\0a\naaa\U{0008}aaaaaaaaaaa"[n] == '?';
}

// REPEAT 4 - TIME: 103.935197 s
