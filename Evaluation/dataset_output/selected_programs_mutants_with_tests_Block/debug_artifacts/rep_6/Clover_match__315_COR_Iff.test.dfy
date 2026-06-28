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
expect |"\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"| == |"\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}", "\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"| ==> "\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"[n] == "\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"[n] || "\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"[n] == '?';
}
method {:test} Test16() {
expect |"\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0008}aaaaaa\U{0002}a"| == |"\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0006}aaaaaa\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0008}aaaaaa\U{0002}a", "\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0006}aaaaaa\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0008}aaaaaa\U{0002}a"| ==> "\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0008}aaaaaa\U{0002}a"[n] == "\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0006}aaaaaa\U{0002}a"[n] || "\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0006}aaaaaa\U{0002}a"[n] == '?';
}
method {:test} Test17() {
expect |"aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"| == |"aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a", "aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"| ==> "aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"[n] == "aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"[n] || "aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"[n] == '?';
}

// REPEAT 6 - TIME: 10.3683282 s
