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

method {:test} Test34() {
expect |"\U{0007}aaaaaa\U{0003}aaaaaaaaaaa\U{0005}aaaaaaa\U{0001}"| == |"?aaaaaa?aaa?aaaaaaa?aaaa?aa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0007}aaaaaa\U{0003}aaaaaaaaaaa\U{0005}aaaaaaa\U{0001}", "?aaaaaa?aaa?aaaaaaa?aaaa?aa?");
expect r0 <==> forall n :: 0 <= n < |"\U{0007}aaaaaa\U{0003}aaaaaaaaaaa\U{0005}aaaaaaa\U{0001}"| ==> "\U{0007}aaaaaa\U{0003}aaaaaaaaaaa\U{0005}aaaaaaa\U{0001}"[n] == "?aaaaaa?aaa?aaaaaaa?aaaa?aa?"[n] || "?aaaaaa?aaa?aaaaaaa?aaaa?aa?"[n] == '?';
}
method {:test} Test35() {
expect |"aaaaa\0\U{0004}aa\U{0008}\n"| == |"\U{000C}aaaa\U{0002}aaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0\U{0004}aa\U{0008}\n", "\U{000C}aaaa\U{0002}aaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0\U{0004}aa\U{0008}\n"| ==> "aaaaa\0\U{0004}aa\U{0008}\n"[n] == "\U{000C}aaaa\U{0002}aaaa\U{0006}"[n] || "\U{000C}aaaa\U{0002}aaaa\U{0006}"[n] == '?';
}

// REPEAT 9 - TIME: 19.3476155 s
