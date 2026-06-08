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

method {:test} Test14() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}aa\U{000B}aaaaaaaa\U{0003}\U{0001}aaa\U{0007}\t"| == |"aaa??aaaaaaaaaa?aaaaaa?aa?aa?aaaaaaaa??aaa??"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}aa\U{000B}aaaaaaaa\U{0003}\U{0001}aaa\U{0007}\t", "aaa??aaaaaaaaaa?aaaaaa?aa?aa?aaaaaaaa??aaa??");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}aa\U{000B}aaaaaaaa\U{0003}\U{0001}aaa\U{0007}\t"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}aa\U{000B}aaaaaaaa\U{0003}\U{0001}aaa\U{0007}\t"[n] == "aaa??aaaaaaaaaa?aaaaaa?aa?aa?aaaaaaaa??aaa??"[n] || "aaa??aaaaaaaaaa?aaaaaa?aa?aa?aaaaaaaa??aaa??"[n] == '?';
}
method {:test} Test15() {
expect |"\U{000C}aa\U{0004}a"| == |"\n\U{0006}\U{0002}\0\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{000C}aa\U{0004}a", "\n\U{0006}\U{0002}\0\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\U{000C}aa\U{0004}a"| ==> "\U{000C}aa\U{0004}a"[n] == "\n\U{0006}\U{0002}\0\U{0008}"[n] || "\n\U{0006}\U{0002}\0\U{0008}"[n] == '?';
}

// REPEAT 8 - TIME: 13.090507 s
