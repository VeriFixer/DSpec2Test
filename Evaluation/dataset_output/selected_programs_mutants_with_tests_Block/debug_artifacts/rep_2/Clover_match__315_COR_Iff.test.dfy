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
expect |"a\0"| == |"a\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0", "a\0");
expect r0 <==> forall n :: 0 <= n < |"a\0"| ==> "a\0"[n] == "a\0"[n] || "a\0"[n] == '?';
}
method {:test} Test4() {
expect |"\na\U{0002}aaaaa\U{0004}"| == |"\U{0006}\0aaaaaa\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\na\U{0002}aaaaa\U{0004}", "\U{0006}\0aaaaaa\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\na\U{0002}aaaaa\U{0004}"| ==> "\na\U{0002}aaaaa\U{0004}"[n] == "\U{0006}\0aaaaaa\U{0008}"[n] || "\U{0006}\0aaaaaa\U{0008}"[n] == '?';
}
method {:test} Test5() {
expect |"\0a"| == |"\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0a", "\0a");
expect r0 <==> forall n :: 0 <= n < |"\0a"| ==> "\0a"[n] == "\0a"[n] || "\0a"[n] == '?';
}

// REPEAT 2 - TIME: 4.4192013 s
