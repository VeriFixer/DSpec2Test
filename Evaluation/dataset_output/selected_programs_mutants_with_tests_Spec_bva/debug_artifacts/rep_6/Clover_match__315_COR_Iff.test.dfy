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

method {:test} Test28() {
expect |"aaaaaaa\U{0004}\U{0002}aaaaa\U{0008}\U{000E}a\U{0006}aaaaaaaa\n\0\U{000C}"| == |"aaaaaaa\U{0004}\U{0002}aaaaa\U{0008}\U{000E}a\U{0006}aaaaaaaa\n\0\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\U{0004}\U{0002}aaaaa\U{0008}\U{000E}a\U{0006}aaaaaaaa\n\0\U{000C}", "aaaaaaa\U{0004}\U{0002}aaaaa\U{0008}\U{000E}a\U{0006}aaaaaaaa\n\0\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\U{0004}\U{0002}aaaaa\U{0008}\U{000E}a\U{0006}aaaaaaaa\n\0\U{000C}"| ==> "aaaaaaa\U{0004}\U{0002}aaaaa\U{0008}\U{000E}a\U{0006}aaaaaaaa\n\0\U{000C}"[n] == "aaaaaaa\U{0004}\U{0002}aaaaa\U{0008}\U{000E}a\U{0006}aaaaaaaa\n\0\U{000C}"[n] || "aaaaaaa\U{0004}\U{0002}aaaaa\U{0008}\U{000E}a\U{0006}aaaaaaaa\n\0\U{000C}"[n] == '?';
}
method {:test} Test29() {
expect |"\U{0006}a\0a\n\U{000C}"| == |"\U{000E}a\U{0002}a\U{0004}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}a\0a\n\U{000C}", "\U{000E}a\U{0002}a\U{0004}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}a\0a\n\U{000C}"| ==> "\U{0006}a\0a\n\U{000C}"[n] == "\U{000E}a\U{0002}a\U{0004}\U{0008}"[n] || "\U{000E}a\U{0002}a\U{0004}\U{0008}"[n] == '?';
}

// REPEAT 6 - TIME: 18.8515768 s
