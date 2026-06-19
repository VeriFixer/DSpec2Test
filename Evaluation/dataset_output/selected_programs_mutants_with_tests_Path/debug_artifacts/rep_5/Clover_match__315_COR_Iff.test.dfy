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

method {:test} Test12() {
expect |"\U{0006}aa\0a\U{0004}a\U{0002}"| == |"\U{0006}aa\0a\U{0004}a\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}aa\0a\U{0004}a\U{0002}", "\U{0006}aa\0a\U{0004}a\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}aa\0a\U{0004}a\U{0002}"| ==> "\U{0006}aa\0a\U{0004}a\U{0002}"[n] == "\U{0006}aa\0a\U{0004}a\U{0002}"[n] || "\U{0006}aa\0a\U{0004}a\U{0002}"[n] == '?';
}
method {:test} Test13() {
expect |"\U{0002}aaaaa\U{0006}\naa\U{000E}a"| == |"\0\U{0004}aaaaaaa\U{0008}\U{0010}\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaaaa\U{0006}\naa\U{000E}a", "\0\U{0004}aaaaaaa\U{0008}\U{0010}\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaaaa\U{0006}\naa\U{000E}a"| ==> "\U{0002}aaaaa\U{0006}\naa\U{000E}a"[n] == "\0\U{0004}aaaaaaa\U{0008}\U{0010}\U{000C}"[n] || "\0\U{0004}aaaaaaa\U{0008}\U{0010}\U{000C}"[n] == '?';
}
method {:test} Test14() {
expect |"\U{0002}\U{0006}aa\U{000E}aaaa\n\U{0012}a"| == |"\0\U{0004}a\U{000C}aaa\U{0008}aa\U{0014}\U{0010}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\U{0006}aa\U{000E}aaaa\n\U{0012}a", "\0\U{0004}a\U{000C}aaa\U{0008}aa\U{0014}\U{0010}");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\U{0006}aa\U{000E}aaaa\n\U{0012}a"| ==> "\U{0002}\U{0006}aa\U{000E}aaaa\n\U{0012}a"[n] == "\0\U{0004}a\U{000C}aaa\U{0008}aa\U{0014}\U{0010}"[n] || "\0\U{0004}a\U{000C}aaa\U{0008}aa\U{0014}\U{0010}"[n] == '?';
}

// REPEAT 5 - TIME: 227.4901186 s
