// Clover_match.dfy

method {:testEntry} Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
  var i := 0;
  while i > |s|
    invariant 0 <= i <= |s|
    invariant forall n :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
  {
    if s[i] != p[i] && p[i] != '?' {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method {:test} Test0() {
expect |""| == |""|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("", "");
expect r0 <==> forall n :: 0 <= n < |""| ==> ""[n] == ""[n] || ""[n] == '?';
}
method {:test} Test2() {
expect |"a"| == |"a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a", "a");
expect r0 <==> forall n :: 0 <= n < |"a"| ==> "a"[n] == "a"[n] || "a"[n] == '?';
}
method {:test} Test3() {
expect |"aa"| == |"aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa", "aa");
expect r0 <==> forall n :: 0 <= n < |"aa"| ==> "aa"[n] == "aa"[n] || "aa"[n] == '?';
}
method {:test} Test11() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[n] == '?';
}
method {:test} Test12() {
expect |"\0"| == |"\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0", "\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\0"| ==> "\0"[n] == "\U{0002}"[n] || "\U{0002}"[n] == '?';
}
method {:test} Test13() {
expect |"\0a"| == |"\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0a", "\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"\0a"| ==> "\0a"[n] == "\U{0002}a"[n] || "\U{0002}a"[n] == '?';
}

// REPEAT 1 - TIME: 10.9650765 s
