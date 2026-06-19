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

method {:test} Test4() {
expect |"\U{0001}"| == |"?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}", "?");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}"| ==> "\U{0001}"[n] == "?"[n] || "?"[n] == '?';
}
method {:test} Test5() {
expect |"\U{0004}aaaa\U{0006}aaaaa"| == |"\0aaaa\U{0008}aaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaa\U{0006}aaaaa", "\0aaaa\U{0008}aaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaa\U{0006}aaaaa"| ==> "\U{0004}aaaa\U{0006}aaaaa"[n] == "\0aaaa\U{0008}aaaa\U{0002}"[n] || "\0aaaa\U{0008}aaaa\U{0002}"[n] == '?';
}

// REPEAT 3 - TIME: 6.1157601 s
