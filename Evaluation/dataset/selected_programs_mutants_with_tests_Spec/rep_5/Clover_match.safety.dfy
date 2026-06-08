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

method {:test} Test8() {
expect |"aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"| == |"aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}", "aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"| ==> "aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"[n] == "aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"[n] || "aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"[n] == '?';
}
method {:test} Test9() {
expect |"a\0\U{0002}\U{0006}"| == |"\na\U{0004}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0\U{0002}\U{0006}", "\na\U{0004}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"a\0\U{0002}\U{0006}"| ==> "a\0\U{0002}\U{0006}"[n] == "\na\U{0004}\U{0008}"[n] || "\na\U{0004}\U{0008}"[n] == '?';
}

// REPEAT 5 - TIME: 8.6754506 s
