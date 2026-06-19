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


method {:test} Test0() {
expect |""| == |""|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("", "");
expect r0 <==> forall n :: 0 <= n < |""| ==> ""[n] == ""[n] || ""[n] == '?';
}
method {:test} Test1() {
expect |"aaaaaaaa\0"| == |"aaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaa\0", "aaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaa\0"| ==> "aaaaaaaa\0"[n] == "aaaaaaaa\U{0002}"[n] || "aaaaaaaa\U{0002}"[n] == '?';
}

// REPEAT 1 - TIME: 3.3760608 s

method {:test} Test2() {
expect |"aaaaaaaaa\U{0001}"| == |"aaaaaaaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\U{0001}", "aaaaaaaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\U{0001}"| ==> "aaaaaaaaa\U{0001}"[n] == "aaaaaaaaa?"[n] || "aaaaaaaaa?"[n] == '?';
}
method {:test} Test3() {
expect |"aaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"| == |"aaaaaaaa\U{0004}\0aaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}", "aaaaaaaa\U{0004}\0aaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"| ==> "aaaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}"[n] == "aaaaaaaa\U{0004}\0aaaaaaaaaaaa"[n] || "aaaaaaaa\U{0004}\0aaaaaaaaaaaa"[n] == '?';
}

// REPEAT 2 - TIME: 4.8666015 s

method {:test} Test4() {
expect |"\U{0001}"| == |"?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}", "?");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}"| ==> "\U{0001}"[n] == "?"[n] || "?"[n] == '?';
}
method {:test} Test5() {
expect |"\U{0004}aaaa\U{0006}aaaaa"| == |"\0aaaa\U{0008}aaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaa\U{0006}aaaaa", "\0aaaa\U{0008}aaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaa\U{0006}aaaaa"| ==> "\U{0004}aaaa\U{0006}aaaaa"[n] == "\0aaaa\U{0008}aaaa\U{0002}"[n] || "\0aaaa\U{0008}aaaa\U{0002}"[n] == '?';
}

// REPEAT 3 - TIME: 6.1157601 s

method {:test} Test6() {
expect |"\U{0001}a"| == |"?a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}a", "?a");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}a"| ==> "\U{0001}a"[n] == "?a"[n] || "?a"[n] == '?';
}
method {:test} Test7() {
expect |"\naaaa\0aaaa\U{0006}"| == |"\U{0008}aaaa\U{0002}aaa\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naaaa\0aaaa\U{0006}", "\U{0008}aaaa\U{0002}aaa\U{0004}a");
expect r0 <==> forall n :: 0 <= n < |"\naaaa\0aaaa\U{0006}"| ==> "\naaaa\0aaaa\U{0006}"[n] == "\U{0008}aaaa\U{0002}aaa\U{0004}a"[n] || "\U{0008}aaaa\U{0002}aaa\U{0004}a"[n] == '?';
}

// REPEAT 4 - TIME: 7.3880927 s

method {:test} Test8() {
expect |"\U{0004}\U{0002}\0"| == |"\U{0004}\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\U{0002}\0", "\U{0004}\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\U{0002}\0"| ==> "\U{0004}\U{0002}\0"[n] == "\U{0004}\U{0002}\0"[n] || "\U{0004}\U{0002}\0"[n] == '?';
}
method {:test} Test9() {
expect |"\U{000C}aaaa\0aaa\U{0006}\n"| == |"\U{0004}aaaa\U{0002}aaa\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{000C}aaaa\0aaa\U{0006}\n", "\U{0004}aaaa\U{0002}aaa\U{0008}a");
expect r0 <==> forall n :: 0 <= n < |"\U{000C}aaaa\0aaa\U{0006}\n"| ==> "\U{000C}aaaa\0aaa\U{0006}\n"[n] == "\U{0004}aaaa\U{0002}aaa\U{0008}a"[n] || "\U{0004}aaaa\U{0002}aaa\U{0008}a"[n] == '?';
}

// REPEAT 5 - TIME: 8.4505857 s

method {:test} Test10() {
expect |"\U{0008}aa\U{0002}\U{0004}aa\0a\U{0006}"| == |"\U{0008}aa\U{0002}\U{0004}aa\0a\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}aa\U{0002}\U{0004}aa\0a\U{0006}", "\U{0008}aa\U{0002}\U{0004}aa\0a\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}aa\U{0002}\U{0004}aa\0a\U{0006}"| ==> "\U{0008}aa\U{0002}\U{0004}aa\0a\U{0006}"[n] == "\U{0008}aa\U{0002}\U{0004}aa\0a\U{0006}"[n] || "\U{0008}aa\U{0002}\U{0004}aa\0a\U{0006}"[n] == '?';
}
method {:test} Test11() {
expect |"\na\U{0004}\U{0006}"| == |"\U{0008}a\0\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\na\U{0004}\U{0006}", "\U{0008}a\0\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\na\U{0004}\U{0006}"| ==> "\na\U{0004}\U{0006}"[n] == "\U{0008}a\0\U{0002}"[n] || "\U{0008}a\0\U{0002}"[n] == '?';
}

// REPEAT 6 - TIME: 9.2871539 s

method {:test} Test12() {
expect |"\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"| == |"\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}", "\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"| ==> "\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"[n] == "\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"[n] || "\0aaaaaaa\U{0002}\U{0004}a\naaaaaaaa\U{0008}\U{0006}\U{000C}"[n] == '?';
}
method {:test} Test13() {
expect |"\naa\0\U{0008}"| == |"\U{000C}\U{0002}a\U{0006}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naa\0\U{0008}", "\U{000C}\U{0002}a\U{0006}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\naa\0\U{0008}"| ==> "\naa\0\U{0008}"[n] == "\U{000C}\U{0002}a\U{0006}\U{0004}"[n] || "\U{000C}\U{0002}a\U{0006}\U{0004}"[n] == '?';
}

// REPEAT 7 - TIME: 10.0399619 s

method {:test} Test14() {
expect |"\U{0006}a\0a\U{0002}\U{0004}"| == |"\U{0006}a\0a\U{0002}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}a\0a\U{0002}\U{0004}", "\U{0006}a\0a\U{0002}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}a\0a\U{0002}\U{0004}"| ==> "\U{0006}a\0a\U{0002}\U{0004}"[n] == "\U{0006}a\0a\U{0002}\U{0004}"[n] || "\U{0006}a\0a\U{0002}\U{0004}"[n] == '?';
}
method {:test} Test15() {
expect |"\U{0012}a\0aaaaaaa\U{0010}\n"| == |"\U{0006}a\U{0002}aa\U{000C}\U{0004}aa\U{0008}a\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0012}a\0aaaaaaa\U{0010}\n", "\U{0006}a\U{0002}aa\U{000C}\U{0004}aa\U{0008}a\U{000E}");
expect r0 <==> forall n :: 0 <= n < |"\U{0012}a\0aaaaaaa\U{0010}\n"| ==> "\U{0012}a\0aaaaaaa\U{0010}\n"[n] == "\U{0006}a\U{0002}aa\U{000C}\U{0004}aa\U{0008}a\U{000E}"[n] || "\U{0006}a\U{0002}aa\U{000C}\U{0004}aa\U{0008}a\U{000E}"[n] == '?';
}

// REPEAT 8 - TIME: 10.8113782 s

method {:test} Test16() {
expect |"aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"| == |"aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n", "aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"| ==> "aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"[n] == "aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"[n] || "aaaaaa\U{0002}aa\U{0006}a\U{0004}aaaa\0\U{0008}aaaaa\U{000E}aaaa\U{000C}\n"[n] == '?';
}
method {:test} Test17() {
expect |"aaaaaaaaaaaaa\U{0008}\0aaaaaaa\U{000C}\U{000E}"| == |"aaaaaaaaaaaaa\n\U{0002}aaaa\U{0004}aaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\U{0008}\0aaaaaaa\U{000C}\U{000E}", "aaaaaaaaaaaaa\n\U{0002}aaaa\U{0004}aaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\U{0008}\0aaaaaaa\U{000C}\U{000E}"| ==> "aaaaaaaaaaaaa\U{0008}\0aaaaaaa\U{000C}\U{000E}"[n] == "aaaaaaaaaaaaa\n\U{0002}aaaa\U{0004}aaa\U{0006}"[n] || "aaaaaaaaaaaaa\n\U{0002}aaaa\U{0004}aaa\U{0006}"[n] == '?';
}

// REPEAT 9 - TIME: 11.620494 s

method {:test} Test18() {
expect |"\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"| == |"\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n", "\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"| ==> "\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"[n] == "\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"[n] || "\U{0004}a\0aaaaaa\U{0006}aaaaaaa\U{0002}aaaa\U{0008}a\n"[n] == '?';
}
method {:test} Test19() {
expect |"\U{0016}aaaaaaaaaaaa\0\U{0006}aaaaa\U{0008}a\naa"| == |"\U{0014}aaaa\U{000E}aa\U{0004}aa\U{0010}a\U{0002}aaaa\U{000C}aa\U{0012}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0016}aaaaaaaaaaaa\0\U{0006}aaaaa\U{0008}a\naa", "\U{0014}aaaa\U{000E}aa\U{0004}aa\U{0010}a\U{0002}aaaa\U{000C}aa\U{0012}aaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0016}aaaaaaaaaaaa\0\U{0006}aaaaa\U{0008}a\naa"| ==> "\U{0016}aaaaaaaaaaaa\0\U{0006}aaaaa\U{0008}a\naa"[n] == "\U{0014}aaaa\U{000E}aa\U{0004}aa\U{0010}a\U{0002}aaaa\U{000C}aa\U{0012}aaa"[n] || "\U{0014}aaaa\U{000E}aa\U{0004}aa\U{0010}a\U{0002}aaaa\U{000C}aa\U{0012}aaa"[n] == '?';
}

// REPEAT 10 - TIME: 12.4441612 s
