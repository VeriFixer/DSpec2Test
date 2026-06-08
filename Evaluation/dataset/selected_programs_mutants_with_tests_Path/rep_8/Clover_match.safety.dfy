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

method {:test} Test21() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"[n] == '?';
}
method {:test} Test22() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}aaaaa\U{0004}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}aaaaa\U{0004}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}aaaaa\U{0004}aa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}aaaaa\U{0004}aa"[n] == '?';
}
method {:test} Test23() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa"[n] == '?';
}

// REPEAT 8 - TIME: 163.7045532 s
