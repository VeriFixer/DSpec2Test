// Clover_match.dfy

method {:testEntry} Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
  var i := 0;
  while false
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

method {:test} Test0() {
expect |""| == |""|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("", "");
expect r0 <==> forall n :: 0 <= n < |""| ==> ""[n] == ""[n] || ""[n] == '?';
}
method {:test} Test1() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[n] == '?';
}

// REPEAT 1 - TIME: 3.27968 s

method {:test} Test2() {
expect |"\U{0001}"| == |"?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}", "?");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}"| ==> "\U{0001}"[n] == "?"[n] || "?"[n] == '?';
}
method {:test} Test3() {
expect |"\0"| == |"\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0", "\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\0"| ==> "\0"[n] == "\U{0002}"[n] || "\U{0002}"[n] == '?';
}

// REPEAT 2 - TIME: 4.7326327 s

method {:test} Test4() {
expect |"\U{0003}a\U{0001}"| == |"?a?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0003}a\U{0001}", "?a?");
expect r0 <==> forall n :: 0 <= n < |"\U{0003}a\U{0001}"| ==> "\U{0003}a\U{0001}"[n] == "?a?"[n] || "?a?"[n] == '?';
}
method {:test} Test5() {
expect |"\U{0002}aaaaaaaaaaaa\U{0004}\0"| == |"aaaaaaaaaaaaa\U{0006}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaaaaaaaaaaa\U{0004}\0", "aaaaaaaaaaaaa\U{0006}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaaaaaaaaaaa\U{0004}\0"| ==> "\U{0002}aaaaaaaaaaaa\U{0004}\0"[n] == "aaaaaaaaaaaaa\U{0006}a"[n] || "aaaaaaaaaaaaa\U{0006}a"[n] == '?';
}

// REPEAT 3 - TIME: 6.641982 s

method {:test} Test6() {
expect |"\U{0002}\0"| == |"\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0", "\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0"| ==> "\U{0002}\0"[n] == "\U{0002}\0"[n] || "\U{0002}\0"[n] == '?';
}
method {:test} Test7() {
expect |"\U{0006}\U{0002}"| == |"\U{0004}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}\U{0002}", "\U{0004}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}\U{0002}"| ==> "\U{0006}\U{0002}"[n] == "\U{0004}\0"[n] || "\U{0004}\0"[n] == '?';
}

// REPEAT 4 - TIME: 8.3014723 s

method {:test} Test8() {
expect |"aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"| == |"aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}", "aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"| ==> "aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"[n] == "aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"[n] || "aaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"[n] == '?';
}
method {:test} Test9() {
expect |"a\0\U{0002}\U{0006}"| == |"\na\U{0004}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0\U{0002}\U{0006}", "\na\U{0004}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"a\0\U{0002}\U{0006}"| ==> "a\0\U{0002}\U{0006}"[n] == "\na\U{0004}\U{0008}"[n] || "\na\U{0004}\U{0008}"[n] == '?';
}

// REPEAT 5 - TIME: 9.6080875 s

method {:test} Test10() {
expect |"\U{0004}\0\U{0002}a"| == |"????"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\0\U{0002}a", "????");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\0\U{0002}a"| ==> "\U{0004}\0\U{0002}a"[n] == "????"[n] || "????"[n] == '?';
}
method {:test} Test11() {
expect |"\U{0010}aa\naa\0a\U{0006}\U{0012}aaaaa\U{0018}"| == |"\U{001A}a\U{0004}aa\U{0014}\U{0002}a\U{000C}a\U{0008}aa\U{000E}a\U{0016}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0010}aa\naa\0a\U{0006}\U{0012}aaaaa\U{0018}", "\U{001A}a\U{0004}aa\U{0014}\U{0002}a\U{000C}a\U{0008}aa\U{000E}a\U{0016}");
expect r0 <==> forall n :: 0 <= n < |"\U{0010}aa\naa\0a\U{0006}\U{0012}aaaaa\U{0018}"| ==> "\U{0010}aa\naa\0a\U{0006}\U{0012}aaaaa\U{0018}"[n] == "\U{001A}a\U{0004}aa\U{0014}\U{0002}a\U{000C}a\U{0008}aa\U{000E}a\U{0016}"[n] || "\U{001A}a\U{0004}aa\U{0014}\U{0002}a\U{000C}a\U{0008}aa\U{000E}a\U{0016}"[n] == '?';
}

// REPEAT 6 - TIME: 11.0988521 s

method {:test} Test12() {
expect |"aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"| == |"aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}", "aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"| ==> "aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"[n] == "aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"[n] || "aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"[n] == '?';
}
method {:test} Test13() {
expect |"aaaaaaaaaaaaaaaa\U{0012}aaaaaaaa\U{0006}aaaaaaaaaaa\n\0a\U{0014}"| == |"aaa\U{0004}aaa\U{000C}\U{0008}aaaaaa\U{000E}aaaaaaaaaa\U{0010}aaaaaaaaaaa\U{0002}\U{0016}\U{0018}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaa\U{0012}aaaaaaaa\U{0006}aaaaaaaaaaa\n\0a\U{0014}", "aaa\U{0004}aaa\U{000C}\U{0008}aaaaaa\U{000E}aaaaaaaaaa\U{0010}aaaaaaaaaaa\U{0002}\U{0016}\U{0018}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaa\U{0012}aaaaaaaa\U{0006}aaaaaaaaaaa\n\0a\U{0014}"| ==> "aaaaaaaaaaaaaaaa\U{0012}aaaaaaaa\U{0006}aaaaaaaaaaa\n\0a\U{0014}"[n] == "aaa\U{0004}aaa\U{000C}\U{0008}aaaaaa\U{000E}aaaaaaaaaa\U{0010}aaaaaaaaaaa\U{0002}\U{0016}\U{0018}"[n] || "aaa\U{0004}aaa\U{000C}\U{0008}aaaaaa\U{000E}aaaaaaaaaa\U{0010}aaaaaaaaaaa\U{0002}\U{0016}\U{0018}"[n] == '?';
}

// REPEAT 7 - TIME: 12.4887962 s

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

// REPEAT 8 - TIME: 13.7299071 s

method {:test} Test16() {
expect |"a\U{0002}a\U{0004}\U{0006}\0"| == |"a\U{0002}a\U{0004}\U{0006}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0002}a\U{0004}\U{0006}\0", "a\U{0002}a\U{0004}\U{0006}\0");
expect r0 <==> forall n :: 0 <= n < |"a\U{0002}a\U{0004}\U{0006}\0"| ==> "a\U{0002}a\U{0004}\U{0006}\0"[n] == "a\U{0002}a\U{0004}\U{0006}\0"[n] || "a\U{0002}a\U{0004}\U{0006}\0"[n] == '?';
}
method {:test} Test17() {
expect |"\U{0014}aaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}aa\0aa\U{0010}"| == |"aaaaaaaaaaaaaaa\U{000C}aaaaaa\U{0006}aaaaa\U{0008}aaaaaaaaa\U{0002}a\U{0004}\U{0012}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0014}aaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}aa\0aa\U{0010}", "aaaaaaaaaaaaaaa\U{000C}aaaaaa\U{0006}aaaaa\U{0008}aaaaaaaaa\U{0002}a\U{0004}\U{0012}");
expect r0 <==> forall n :: 0 <= n < |"\U{0014}aaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}aa\0aa\U{0010}"| ==> "\U{0014}aaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}aa\0aa\U{0010}"[n] == "aaaaaaaaaaaaaaa\U{000C}aaaaaa\U{0006}aaaaa\U{0008}aaaaaaaaa\U{0002}a\U{0004}\U{0012}"[n] || "aaaaaaaaaaaaaaa\U{000C}aaaaaa\U{0006}aaaaa\U{0008}aaaaaaaaa\U{0002}a\U{0004}\U{0012}"[n] == '?';
}

// REPEAT 9 - TIME: 15.0419397 s

method {:test} Test18() {
expect |"\U{0007}aaaaaaaaaa\U{0005}\U{0001}aaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaa\taaaa"| == |"?aaaaaaaaaa??aa?aaaaaa?aaaaaaaa?aaaaaa????aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0007}aaaaaaaaaa\U{0005}\U{0001}aaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaa\taaaa", "?aaaaaaaaaa??aa?aaaaaa?aaaaaaaa?aaaaaa????aaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0007}aaaaaaaaaa\U{0005}\U{0001}aaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaa\taaaa"| ==> "\U{0007}aaaaaaaaaa\U{0005}\U{0001}aaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaa\taaaa"[n] == "?aaaaaaaaaa??aa?aaaaaa?aaaaaaaa?aaaaaa????aaa"[n] || "?aaaaaaaaaa??aa?aaaaaa?aaaaaaaa?aaaaaa????aaa"[n] == '?';
}
method {:test} Test19() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}aaa\U{0006}aaaaaaaaaaaaaa\U{0010}"| == |"aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaa\U{0002}aaaaaaaaaaaa\na\U{000C}\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}aaa\U{0006}aaaaaaaaaaaaaa\U{0010}", "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaa\U{0002}aaaaaaaaaaaa\na\U{000C}\U{000E}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}aaa\U{0006}aaaaaaaaaaaaaa\U{0010}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}aaa\U{0006}aaaaaaaaaaaaaa\U{0010}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaa\U{0002}aaaaaaaaaaaa\na\U{000C}\U{000E}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaa\U{0002}aaaaaaaaaaaa\na\U{000C}\U{000E}"[n] == '?';
}

// REPEAT 10 - TIME: 16.55676 s
