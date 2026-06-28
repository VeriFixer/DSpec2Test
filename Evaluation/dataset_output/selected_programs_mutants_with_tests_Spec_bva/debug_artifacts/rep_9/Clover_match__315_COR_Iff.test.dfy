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

method {:test} Test34() {
expect |"\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"| == |"\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}", "\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"| ==> "\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"[n] == "\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"[n] || "\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"[n] == '?';
}
method {:test} Test35() {
expect |"\U{0014}aaaaaa\U{0006}aa\0a\U{000C}\U{0008}"| == |"\U{0012}aaaaaa\U{0004}aa\U{0002}\n\U{000E}\U{0010}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0014}aaaaaa\U{0006}aa\0a\U{000C}\U{0008}", "\U{0012}aaaaaa\U{0004}aa\U{0002}\n\U{000E}\U{0010}");
expect r0 <==> forall n :: 0 <= n < |"\U{0014}aaaaaa\U{0006}aa\0a\U{000C}\U{0008}"| ==> "\U{0014}aaaaaa\U{0006}aa\0a\U{000C}\U{0008}"[n] == "\U{0012}aaaaaa\U{0004}aa\U{0002}\n\U{000E}\U{0010}"[n] || "\U{0012}aaaaaa\U{0004}aa\U{0002}\n\U{000E}\U{0010}"[n] == '?';
}

// REPEAT 9 - TIME: 25.2364732 s
