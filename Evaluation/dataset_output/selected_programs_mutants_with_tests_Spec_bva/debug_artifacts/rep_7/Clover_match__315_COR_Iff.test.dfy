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

method {:test} Test30() {
expect |"aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"| == |"aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}", "aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"| ==> "aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"[n] == "aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"[n] || "aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"[n] == '?';
}
method {:test} Test31() {
expect |"aa\0aa\U{0004}\U{0006}aa\U{000E}\U{000C}\U{0010}"| == |"aa\U{0002}aaaaaa\n\U{0008}\U{0012}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0aa\U{0004}\U{0006}aa\U{000E}\U{000C}\U{0010}", "aa\U{0002}aaaaaa\n\U{0008}\U{0012}");
expect r0 <==> forall n :: 0 <= n < |"aa\0aa\U{0004}\U{0006}aa\U{000E}\U{000C}\U{0010}"| ==> "aa\0aa\U{0004}\U{0006}aa\U{000E}\U{000C}\U{0010}"[n] == "aa\U{0002}aaaaaa\n\U{0008}\U{0012}"[n] || "aa\U{0002}aaaaaa\n\U{0008}\U{0012}"[n] == '?';
}

// REPEAT 7 - TIME: 22.507467 s
