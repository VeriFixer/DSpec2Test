method {:testEntry} Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall n :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
  {
    if s[i] != p[i] && p[i] != '?'
    {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method {:test} Test16() {
expect |"a\U{0002}a\U{0004}\U{0006}\0"| == |"a\U{0002}a\U{0004}\U{0006}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0002}a\U{0004}\U{0006}\0", "a\U{0002}a\U{0004}\U{0006}\0");
expect r0 <==> forall n :: 0 <= n < |"a\U{0002}a\U{0004}\U{0006}\0"| ==> "a\U{0002}a\U{0004}\U{0006}\0"[n] == "a\U{0002}a\U{0004}\U{0006}\0"[n] || "a\U{0002}a\U{0004}\U{0006}\0"[n] == '?';
}
method {:test} Test17() {
expect |"\U{0014}aaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}aa\0aa\U{0010}"| == |"aaaaaaaaaaaaaaa\U{000C}aaaaaa\U{0006}aaaaa\U{0008}aaaaaaaaa\U{0002}a\U{0004}\U{0012}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0014}aaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}aa\0aa\U{0010}", "aaaaaaaaaaaaaaa\U{000C}aaaaaa\U{0006}aaaaa\U{0008}aaaaaaaaa\U{0002}a\U{0004}\U{0012}");
expect r0 <==> forall n :: 0 <= n < |"\U{0014}aaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}aa\0aa\U{0010}"| ==> "\U{0014}aaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}aa\0aa\U{0010}"[n] == "aaaaaaaaaaaaaaa\U{000C}aaaaaa\U{0006}aaaaa\U{0008}aaaaaaaaa\U{0002}a\U{0004}\U{0012}"[n] || "aaaaaaaaaaaaaaa\U{000C}aaaaaa\U{0006}aaaaa\U{0008}aaaaaaaaa\U{0002}a\U{0004}\U{0012}"[n] == '?';
}

// REPEAT 9 - TIME: 14.4450323 s
