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

method {:test} Test6() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[n] == '?';
}
method {:test} Test7() {
expect |"\U{0008}\U{0002}\U{0006}"| == |"\n\0\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}\U{0002}\U{0006}", "\n\0\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}\U{0002}\U{0006}"| ==> "\U{0008}\U{0002}\U{0006}"[n] == "\n\0\U{0004}"[n] || "\n\0\U{0004}"[n] == '?';
}
method {:test} Test8() {
expect |"\naaaaaa\U{0006}aaaa\U{0002}aaaaa"| == |"\U{0008}\0aaaaaaaaaaaaaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naaaaaa\U{0006}aaaa\U{0002}aaaaa", "\U{0008}\0aaaaaaaaaaaaaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\naaaaaa\U{0006}aaaa\U{0002}aaaaa"| ==> "\naaaaaa\U{0006}aaaa\U{0002}aaaaa"[n] == "\U{0008}\0aaaaaaaaaaaaaaa\U{0004}"[n] || "\U{0008}\0aaaaaaaaaaaaaaa\U{0004}"[n] == '?';
}

// REPEAT 3 - TIME: 67.991816 s
