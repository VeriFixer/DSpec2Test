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
expect |"a"| == |"a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a", "a");
expect r0 <==> forall n :: 0 <= n < |"a"| ==> "a"[n] == "a"[n] || "a"[n] == '?';
}
method {:test} Test1() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[n] == '?';
}
method {:test} Test2() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == '?';
}

// REPEAT 1 - TIME: 2.8814459 s

method {:test} Test3() {
expect |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}", "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"[n] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"[n] || "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"[n] == '?';
}
method {:test} Test4() {
expect |"a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0008}\U{0006}"| == |"a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0008}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0008}\U{0006}", "a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0008}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0008}\U{0006}"| ==> "a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0008}\U{0006}"[n] == "a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0008}\U{0006}"[n] || "a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0008}\U{0006}"[n] == '?';
}
method {:test} Test5() {
expect |"a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"| == |"a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a", "a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a");
expect r0 <==> forall n :: 0 <= n < |"a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"| ==> "a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"[n] == "a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"[n] || "a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"[n] == '?';
}

// REPEAT 2 - TIME: 4.6230927 s

method {:test} Test6() {
expect |"\U{0002}\0"| == |"\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0", "\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0"| ==> "\U{0002}\0"[n] == "\U{0002}\0"[n] || "\U{0002}\0"[n] == '?';
}
method {:test} Test7() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"[n] == '?';
}
method {:test} Test8() {
expect |"\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"| == |"\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0", "\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"| ==> "\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"[n] == "\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"[n] || "\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"[n] == '?';
}

// REPEAT 3 - TIME: 6.4985325 s

method {:test} Test9() {
expect |"\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"| == |"\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n", "\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"| ==> "\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"[n] == "\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"[n] || "\U{0004}\0\U{000C}\U{000E}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa\U{0006}\U{0008}\n"[n] == '?';
}
method {:test} Test10() {
expect |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"| == |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa", "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa");
expect r0 <==> forall n :: 0 <= n < |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"| ==> "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"[n] == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"[n] || "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000E}\U{0004}\U{0008}a\U{0006}aa\na\U{000C}aa"[n] == '?';
}
method {:test} Test11() {
expect |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}", "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"[n] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"[n] || "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\naaaaaa\U{0008}\U{0006}"[n] == '?';
}

// REPEAT 4 - TIME: 8.628505 s

method {:test} Test12() {
expect |"aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"| == |"aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}", "aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"| ==> "aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"[n] == "aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"[n] || "aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"[n] == '?';
}
method {:test} Test13() {
expect |"aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa"| == |"aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa", "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa"| ==> "aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa"[n] == "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}"[n] || "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}"[n] == '?';
}
method {:test} Test14() {
expect |"\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{000E}a\U{0008}a"| == |"\U{0012}\0a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\na\U{000C}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{000E}a\U{0008}a", "\U{0012}\0a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\na\U{000C}aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{000E}a\U{0008}a"| ==> "\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{000E}a\U{0008}a"[n] == "\U{0012}\0a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\na\U{000C}aaaaaa"[n] || "\U{0012}\0a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\na\U{000C}aaaaaa"[n] == '?';
}

// REPEAT 5 - TIME: 10.718279 s

method {:test} Test15() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == '?';
}
method {:test} Test16() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaa"[n] == '?';
}
method {:test} Test17() {
expect |"\0aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa"| == |"\0aa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa", "\0aa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa"| ==> "\0aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa"[n] == "\0aa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[n] || "\0aa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[n] == '?';
}

// REPEAT 6 - TIME: 12.6096956 s

method {:test} Test18() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa"[n] == '?';
}
method {:test} Test19() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"\U{0002}aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "\U{0002}aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaa"[n] || "\U{0002}aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaa"[n] == '?';
}
method {:test} Test20() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa"[n] == '?';
}

// REPEAT 7 - TIME: 14.6040689 s

method {:test} Test21() {
expect |"aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test22() {
expect |"aaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test23() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| == |"\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[n] == "\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "\0\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 8 - TIME: 17.0007475 s

method {:test} Test24() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test26() {
expect |"aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 9 - TIME: 19.9432664 s

method {:test} Test27() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test28() {
expect |"aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test29() {
expect |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 10 - TIME: 22.8013871 s
