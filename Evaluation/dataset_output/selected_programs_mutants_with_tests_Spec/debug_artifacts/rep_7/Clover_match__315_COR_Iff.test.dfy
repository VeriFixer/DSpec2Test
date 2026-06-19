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

method {:test} Test12() {
expect |"\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"| == |"\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}", "\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"| ==> "\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"[n] == "\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"[n] || "\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"[n] == '?';
}
method {:test} Test13() {
expect |"\naa\0\U{0008}"| == |"\U{000C}\U{0002}a\U{0006}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naa\0\U{0008}", "\U{000C}\U{0002}a\U{0006}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\naa\0\U{0008}"| ==> "\naa\0\U{0008}"[n] == "\U{000C}\U{0002}a\U{0006}\U{0004}"[n] || "\U{000C}\U{0002}a\U{0006}\U{0004}"[n] == '?';
}

// REPEAT 7 - TIME: 10.0399619 s
