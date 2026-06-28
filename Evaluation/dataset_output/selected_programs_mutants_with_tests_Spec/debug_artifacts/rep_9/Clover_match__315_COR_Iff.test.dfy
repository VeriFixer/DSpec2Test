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

method {:test} Test16() {
expect |"aaaaaaaaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaa\0"| == |"aaaaaa?aa?a?aa?a?a?aaaaa?aaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaa\0", "aaaaaa?aa?a?aa?a?a?aaaaa?aaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaa\0"[n] == "aaaaaa?aa?a?aa?a?a?aaaaa?aaaa?"[n] || "aaaaaa?aa?a?aa?a?a?aaaaa?aaaa?"[n] == '?';
}
method {:test} Test17() {
expect |"\naa\0a\U{0006}"| == |"\U{0008}aa\U{0002}a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naa\0a\U{0006}", "\U{0008}aa\U{0002}a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\naa\0a\U{0006}"| ==> "\naa\0a\U{0006}"[n] == "\U{0008}aa\U{0002}a\U{0004}"[n] || "\U{0008}aa\U{0002}a\U{0004}"[n] == '?';
}

// REPEAT 9 - TIME: 14.8719907 s
