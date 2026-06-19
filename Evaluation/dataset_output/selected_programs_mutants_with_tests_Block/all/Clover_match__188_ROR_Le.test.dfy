// Clover_match.dfy

method {:testEntry} Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
  var i := 0;
  while i <= |s|
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
expect |"a"| == |"a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a", "a");
expect r0 <==> forall n :: 0 <= n < |"a"| ==> "a"[n] == "a"[n] || "a"[n] == '?';
}
method {:test} Test1() {
expect |"aaaaaaaaa\0"| == |"aaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\0", "aaaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\0"| ==> "aaaaaaaaa\0"[n] == "aaaaaaaaa\U{0002}"[n] || "aaaaaaaaa\U{0002}"[n] == '?';
}
method {:test} Test2() {
expect |"aaaaaaaaa\0"| == |"aaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\0", "aaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\0"| ==> "aaaaaaaaa\0"[n] == "aaaaaaaaa\0"[n] || "aaaaaaaaa\0"[n] == '?';
}

// REPEAT 1 - TIME: 3.1081475 s

method {:test} Test3() {
expect |"aa\U{0005}aaaaaaaa\0\U{0002}"| == |"a?\U{0005}aaaaaaaa\0\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\U{0005}aaaaaaaa\0\U{0002}", "a?\U{0005}aaaaaaaa\0\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aa\U{0005}aaaaaaaa\0\U{0002}"| ==> "aa\U{0005}aaaaaaaa\0\U{0002}"[n] == "a?\U{0005}aaaaaaaa\0\U{0002}"[n] || "a?\U{0005}aaaaaaaa\0\U{0002}"[n] == '?';
}
method {:test} Test4() {
expect |"a\U{0008}\U{0002}aaaaa\U{0004}"| == |"a\0aaaaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0008}\U{0002}aaaaa\U{0004}", "a\0aaaaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0008}\U{0002}aaaaa\U{0004}"| ==> "a\U{0008}\U{0002}aaaaa\U{0004}"[n] == "a\0aaaaaa\U{0006}"[n] || "a\0aaaaaa\U{0006}"[n] == '?';
}
method {:test} Test5() {
expect |"\U{0006}a\0aaaaaaa\U{0002}"| == |"\U{0006}\U{0008}aaaaaaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}a\0aaaaaaa\U{0002}", "\U{0006}\U{0008}aaaaaaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}a\0aaaaaaa\U{0002}"| ==> "\U{0006}a\0aaaaaaa\U{0002}"[n] == "\U{0006}\U{0008}aaaaaaaa\U{0004}"[n] || "\U{0006}\U{0008}aaaaaaaa\U{0004}"[n] == '?';
}

// REPEAT 2 - TIME: 4.8296483 s

method {:test} Test6() {
expect |"\U{0002}\0"| == |"\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0", "\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0"| ==> "\U{0002}\0"[n] == "\U{0002}\0"[n] || "\U{0002}\0"[n] == '?';
}
method {:test} Test7() {
expect |"a\U{0008}a\0a\U{0006}a\U{0004}"| == |"a\U{0008}a\U{0002}a\U{0006}a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0008}a\0a\U{0006}a\U{0004}", "a\U{0008}a\U{0002}a\U{0006}a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0008}a\0a\U{0006}a\U{0004}"| ==> "a\U{0008}a\0a\U{0006}a\U{0004}"[n] == "a\U{0008}a\U{0002}a\U{0006}a\U{0004}"[n] || "a\U{0008}a\U{0002}a\U{0006}a\U{0004}"[n] == '?';
}

// REPEAT 3 - TIME: 6.6307211 s

method {:test} Test9() {
expect |"aaaaaaa\0a\U{0004}\U{0002}\U{0006}"| == |"aaaaaaa\0a\U{0004}\U{0002}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\0a\U{0004}\U{0002}\U{0006}", "aaaaaaa\0a\U{0004}\U{0002}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\0a\U{0004}\U{0002}\U{0006}"| ==> "aaaaaaa\0a\U{0004}\U{0002}\U{0006}"[n] == "aaaaaaa\0a\U{0004}\U{0002}\U{0006}"[n] || "aaaaaaa\0a\U{0004}\U{0002}\U{0006}"[n] == '?';
}
method {:test} Test10() {
expect |"a\0\U{0006}aa\U{0004}\U{0002}"| == |"a\0\U{0008}aa\U{0004}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0\U{0006}aa\U{0004}\U{0002}", "a\0\U{0008}aa\U{0004}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"a\0\U{0006}aa\U{0004}\U{0002}"| ==> "a\0\U{0006}aa\U{0004}\U{0002}"[n] == "a\0\U{0008}aa\U{0004}\U{0002}"[n] || "a\0\U{0008}aa\U{0004}\U{0002}"[n] == '?';
}
method {:test} Test11() {
expect |"aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"| == |"aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n", "aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"| ==> "aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"[n] == "aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"[n] || "aaaaaaaaa\U{0004}\U{0006}\0aa\U{0002}a\U{0008}a\n"[n] == '?';
}

// REPEAT 4 - TIME: 8.3685015 s

method {:test} Test12() {
expect |"aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"| == |"aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}", "aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"| ==> "aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"[n] == "aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"[n] || "aaaaa\U{0002}a\U{0004}aaa\U{0008}aa\U{000E}aa\U{000C}\U{0006}a\n\0\U{0010}"[n] == '?';
}
method {:test} Test13() {
expect |"\U{0002}aaaaaaaa\U{0006}aaaaaa\U{0012}\U{000C}aa"| == |"\0\U{0004}aaaaaaa\na\U{000E}aaaaa\U{0010}\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaaaaaaa\U{0006}aaaaaa\U{0012}\U{000C}aa", "\0\U{0004}aaaaaaa\na\U{000E}aaaaa\U{0010}\U{0008}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaaaaaaa\U{0006}aaaaaa\U{0012}\U{000C}aa"| ==> "\U{0002}aaaaaaaa\U{0006}aaaaaa\U{0012}\U{000C}aa"[n] == "\0\U{0004}aaaaaaa\na\U{000E}aaaaa\U{0010}\U{0008}a"[n] || "\0\U{0004}aaaaaaa\na\U{000E}aaaaa\U{0010}\U{0008}a"[n] == '?';
}
method {:test} Test14() {
expect |"\0aaaaaaaa\U{0006}aaaaa\na\U{0016}\U{0012}\U{001C}"| == |"\0\U{0002}aaaaa\U{0004}aa\U{000C}\U{0010}a\U{0018}a\U{000E}\U{0014}a\U{0008}\U{001A}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaa\U{0006}aaaaa\na\U{0016}\U{0012}\U{001C}", "\0\U{0002}aaaaa\U{0004}aa\U{000C}\U{0010}a\U{0018}a\U{000E}\U{0014}a\U{0008}\U{001A}");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaa\U{0006}aaaaa\na\U{0016}\U{0012}\U{001C}"| ==> "\0aaaaaaaa\U{0006}aaaaa\na\U{0016}\U{0012}\U{001C}"[n] == "\0\U{0002}aaaaa\U{0004}aa\U{000C}\U{0010}a\U{0018}a\U{000E}\U{0014}a\U{0008}\U{001A}"[n] || "\0\U{0002}aaaaa\U{0004}aa\U{000C}\U{0010}a\U{0018}a\U{000E}\U{0014}a\U{0008}\U{001A}"[n] == '?';
}

// REPEAT 5 - TIME: 9.9871247 s

method {:test} Test15() {
expect |"aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"| == |"aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa", "aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"| ==> "aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"[n] == "aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"[n] || "aaaaaaaaa\U{0004}\0aaa\U{0002}aaa\U{0006}aa"[n] == '?';
}
method {:test} Test16() {
expect |"\0aa"| == |"\U{0002}a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa", "\U{0002}a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\0aa"| ==> "\0aa"[n] == "\U{0002}a\U{0004}"[n] || "\U{0002}a\U{0004}"[n] == '?';
}
method {:test} Test17() {
expect |"aaaaaa\0aaaaaa\U{0002}aaaaa\U{0008}aaa\U{000C}"| == |"aaaaaa\0aa\U{0006}aaaa\U{0004}aaaaaaaa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaa\0aaaaaa\U{0002}aaaaa\U{0008}aaa\U{000C}", "aaaaaa\0aa\U{0006}aaaa\U{0004}aaaaaaaa\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaa\0aaaaaa\U{0002}aaaaa\U{0008}aaa\U{000C}"| ==> "aaaaaa\0aaaaaa\U{0002}aaaaa\U{0008}aaa\U{000C}"[n] == "aaaaaa\0aa\U{0006}aaaa\U{0004}aaaaaaaa\n"[n] || "aaaaaa\0aa\U{0006}aaaa\U{0004}aaaaaaaa\n"[n] == '?';
}

// REPEAT 6 - TIME: 11.5586868 s

method {:test} Test18() {
expect |"\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"| == |"\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}", "\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"| ==> "\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"[n] == "\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"[n] || "\U{0008}aaaaaaaaaaaaaaaa\0a\U{0002}\U{0006}\U{0004}"[n] == '?';
}
method {:test} Test19() {
expect |"aaaaaaaaaaaaaaaaaaa\0aaaa\U{0008}aaaa"| == |"aaaaaaaaaaaaaaaaaaa\na\U{0002}a\U{0004}aaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaa\0aaaa\U{0008}aaaa", "aaaaaaaaaaaaaaaaaaa\na\U{0002}a\U{0004}aaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaa\0aaaa\U{0008}aaaa"| ==> "aaaaaaaaaaaaaaaaaaa\0aaaa\U{0008}aaaa"[n] == "aaaaaaaaaaaaaaaaaaa\na\U{0002}a\U{0004}aaaa\U{0006}"[n] || "aaaaaaaaaaaaaaaaaaa\na\U{0002}a\U{0004}aaaa\U{0006}"[n] == '?';
}
method {:test} Test20() {
expect |"aaaaaaaaaaaa\0aaaaaaaaaaa\U{0006}"| == |"aaaaaaaaaaaa\0aaaaaaaaa\U{0002}\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaa\0aaaaaaaaaaa\U{0006}", "aaaaaaaaaaaa\0aaaaaaaaa\U{0002}\U{0004}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaa\0aaaaaaaaaaa\U{0006}"| ==> "aaaaaaaaaaaa\0aaaaaaaaaaa\U{0006}"[n] == "aaaaaaaaaaaa\0aaaaaaaaa\U{0002}\U{0004}a"[n] || "aaaaaaaaaaaa\0aaaaaaaaa\U{0002}\U{0004}a"[n] == '?';
}

// REPEAT 7 - TIME: 13.3284053 s

method {:test} Test21() {
expect |"aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"| == |"aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a", "aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a");
expect r0 <==> forall n :: 0 <= n < |"aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"| ==> "aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"[n] == "aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"[n] || "aaa\0aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}\U{0006}\U{0008}a"[n] == '?';
}
method {:test} Test22() {
expect |"aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{000C}"| == |"aa\0\U{0004}aaaaaaaaaaaaaaaaa\U{0006}aaa\naaa\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{000C}", "aa\0\U{0004}aaaaaaaaaaaaaaaaa\U{0006}aaa\naaa\U{000E}");
expect r0 <==> forall n :: 0 <= n < |"aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{000C}"| ==> "aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{000C}"[n] == "aa\0\U{0004}aaaaaaaaaaaaaaaaa\U{0006}aaa\naaa\U{000E}"[n] || "aa\0\U{0004}aaaaaaaaaaaaaaaaa\U{0006}aaa\naaa\U{000E}"[n] == '?';
}
method {:test} Test23() {
expect |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n"| == |"aa\0\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}aaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n", "aa\0\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}aaaa");
expect r0 <==> forall n :: 0 <= n < |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n"| ==> "aa\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n"[n] == "aa\0\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}aaaa"[n] || "aa\0\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}aaaa"[n] == '?';
}

// REPEAT 8 - TIME: 14.9192205 s

method {:test} Test24() {
expect |"aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"| == |"aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}", "aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"[n] == "aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"[n] || "aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a\U{0004}"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| == |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa", "aaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[n] == "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] || "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] == '?';
}
method {:test} Test26() {
expect |"aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"| == |"aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a", "aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"| ==> "aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"[n] == "aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"[n] || "aaaaaaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0002}a"[n] == '?';
}

// REPEAT 9 - TIME: 16.4100794 s

method {:test} Test27() {
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"[n] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"[n] || "\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0"[n] == '?';
}
method {:test} Test28() {
expect |"\U{0004}a\U{0002}aaaaaaaaaaaaaaa"| == |"\U{0004}a\0aaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}a\U{0002}aaaaaaaaaaaaaaa", "\U{0004}a\0aaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}a\U{0002}aaaaaaaaaaaaaaa"| ==> "\U{0004}a\U{0002}aaaaaaaaaaaaaaa"[n] == "\U{0004}a\0aaaaaaaaaaaaaaa"[n] || "\U{0004}a\0aaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test29() {
expect |"\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"| == |"\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0", "\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"| ==> "\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"[n] == "\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"[n] || "\U{0004}aaaaaaaaaaaaaa\U{0006}a\U{0002}aaaaa\0"[n] == '?';
}

// REPEAT 10 - TIME: 18.0708215 s
