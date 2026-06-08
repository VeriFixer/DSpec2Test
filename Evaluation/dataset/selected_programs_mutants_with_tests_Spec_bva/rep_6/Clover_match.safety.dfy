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

method {:test} Test28() {
expect |"aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"| == |"aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}", "aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"| ==> "aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"[n] == "aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"[n] || "aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"[n] == '?';
}
method {:test} Test29() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaa\0a\U{0010}\U{0006}\U{000E}"| == |"aaaaaaaaaaaaa\U{0008}\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0012}aa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaa\0a\U{0010}\U{0006}\U{000E}", "aaaaaaaaaaaaa\U{0008}\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0012}aa\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaa\0a\U{0010}\U{0006}\U{000E}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaa\0a\U{0010}\U{0006}\U{000E}"[n] == "aaaaaaaaaaaaa\U{0008}\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0012}aa\n"[n] || "aaaaaaaaaaaaa\U{0008}\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0012}aa\n"[n] == '?';
}

// REPEAT 6 - TIME: 16.4688447 s
