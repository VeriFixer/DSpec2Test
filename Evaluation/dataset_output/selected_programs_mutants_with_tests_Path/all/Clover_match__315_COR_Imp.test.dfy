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
    if s[i] != p[i] ==> p[i] != '?' {
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
expect |"aaaaaaaaa\U{0002}"| == |"aaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\U{0002}", "aaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\U{0002}"| ==> "aaaaaaaaa\U{0002}"[n] == "aaaaaaaaa\0"[n] || "aaaaaaaaa\0"[n] == '?';
}

// REPEAT 1 - TIME: 44.5278828 s

method {:test} Test3() {
expect |"\U{0002}\0"| == |"\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0", "\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0"| ==> "\U{0002}\0"[n] == "\U{0002}\0"[n] || "\U{0002}\0"[n] == '?';
}
method {:test} Test4() {
expect |"\U{0002}\0"| == |"\U{0004}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0", "\U{0004}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0"| ==> "\U{0002}\0"[n] == "\U{0004}\U{0006}"[n] || "\U{0004}\U{0006}"[n] == '?';
}

// REPEAT 2 - TIME: 84.1983257 s

method {:test} Test6() {
expect |"\U{0002}\0aa\U{0004}aaaaa\U{0006}"| == |"\U{0002}\0aa\U{0004}aaaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0aa\U{0004}aaaaa\U{0006}", "\U{0002}\0aa\U{0004}aaaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0aa\U{0004}aaaaa\U{0006}"| ==> "\U{0002}\0aa\U{0004}aaaaa\U{0006}"[n] == "\U{0002}\0aa\U{0004}aaaaa\U{0006}"[n] || "\U{0002}\0aa\U{0004}aaaaa\U{0006}"[n] == '?';
}
method {:test} Test7() {
expect |"\U{0004}\0\U{0006}"| == |"\U{0004}\U{0002}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\0\U{0006}", "\U{0004}\U{0002}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\0\U{0006}"| ==> "\U{0004}\0\U{0006}"[n] == "\U{0004}\U{0002}\U{0006}"[n] || "\U{0004}\U{0002}\U{0006}"[n] == '?';
}

// REPEAT 3 - TIME: 123.9350195 s

method {:test} Test9() {
expect |"\U{0004}aa\U{0006}aaa\U{0002}a\0"| == |"\U{0004}aa\U{0006}aaa\U{0002}a\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aa\U{0006}aaa\U{0002}a\0", "\U{0004}aa\U{0006}aaa\U{0002}a\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aa\U{0006}aaa\U{0002}a\0"| ==> "\U{0004}aa\U{0006}aaa\U{0002}a\0"[n] == "\U{0004}aa\U{0006}aaa\U{0002}a\0"[n] || "\U{0004}aa\U{0006}aaa\U{0002}a\0"[n] == '?';
}
method {:test} Test10() {
expect |"a\U{0008}a\U{0004}"| == |"a\0\U{0002}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0008}a\U{0004}", "a\0\U{0002}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0008}a\U{0004}"| ==> "a\U{0008}a\U{0004}"[n] == "a\0\U{0002}\U{0006}"[n] || "a\0\U{0002}\U{0006}"[n] == '?';
}
method {:test} Test11() {
expect |"\U{0008}aa\U{0002}"| == |"\U{0006}\0a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}aa\U{0002}", "\U{0006}\0a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}aa\U{0002}"| ==> "\U{0008}aa\U{0002}"[n] == "\U{0006}\0a\U{0004}"[n] || "\U{0006}\0a\U{0004}"[n] == '?';
}

// REPEAT 4 - TIME: 173.9586147 s

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

method {:test} Test15() {
expect |"aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"| == |"aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}", "aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"| ==> "aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"[n] == "aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"[n] || "aa\U{0002}aaaaaa\0\U{0004}\U{0006}\U{0008}"[n] == '?';
}
method {:test} Test16() {
expect |"aaaaaaaaaaaaaaaa\U{0006}a\0\U{0008}aaaaaaa\U{0004}"| == |"aaaaaaaaaaaaaaaa\U{0006}a\U{0002}\U{0008}aaaaaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaa\U{0006}a\0\U{0008}aaaaaaa\U{0004}", "aaaaaaaaaaaaaaaa\U{0006}a\U{0002}\U{0008}aaaaaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaa\U{0006}a\0\U{0008}aaaaaaa\U{0004}"| ==> "aaaaaaaaaaaaaaaa\U{0006}a\0\U{0008}aaaaaaa\U{0004}"[n] == "aaaaaaaaaaaaaaaa\U{0006}a\U{0002}\U{0008}aaaaaaa\U{0004}"[n] || "aaaaaaaaaaaaaaaa\U{0006}a\U{0002}\U{0008}aaaaaaa\U{0004}"[n] == '?';
}
method {:test} Test17() {
expect |"aaaaaaaaaaaaa\0aaaa\U{0004}"| == |"aaaaaaaaaaaaa\U{0002}aaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\0aaaa\U{0004}", "aaaaaaaaaaaaa\U{0002}aaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\0aaaa\U{0004}"| ==> "aaaaaaaaaaaaa\0aaaa\U{0004}"[n] == "aaaaaaaaaaaaa\U{0002}aaaa\U{0004}"[n] || "aaaaaaaaaaaaa\U{0002}aaaa\U{0004}"[n] == '?';
}

// REPEAT 6 - TIME: 313.2686165 s

method {:test} Test18() {
expect |"aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"| == |"aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}", "aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"| ==> "aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"[n] == "aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"[n] || "aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa\0aa\U{0006}\U{0008}"[n] == '?';
}
method {:test} Test19() {
expect |"\U{0004}aaaa\0a"| == |"\U{0002}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaa\0a", "\U{0002}aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaa\0a"| ==> "\U{0004}aaaa\0a"[n] == "\U{0002}aaaaaa"[n] || "\U{0002}aaaaaa"[n] == '?';
}

// REPEAT 7 - TIME: 447.8801039 s

method {:test} Test21() {
expect |"\U{0002}aaa\0a"| == |"\U{0002}aaa\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaa\0a", "\U{0002}aaa\0a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaa\0a"| ==> "\U{0002}aaa\0a"[n] == "\U{0002}aaa\0a"[n] || "\U{0002}aaa\0a"[n] == '?';
}
method {:test} Test22() {
expect |"\0aaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}a\n"| == |"\U{000E}aaaaaaaaaaaaaaaaaa\U{0006}aa\U{0002}aaaaa\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}a\n", "\U{000E}aaaaaaaaaaaaaaaaaa\U{0006}aa\U{0002}aaaaa\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}a\n"| ==> "\0aaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}a\n"[n] == "\U{000E}aaaaaaaaaaaaaaaaaa\U{0006}aa\U{0002}aaaaa\U{000C}"[n] || "\U{000E}aaaaaaaaaaaaaaaaaa\U{0006}aa\U{0002}aaaaa\U{000C}"[n] == '?';
}

// REPEAT 8 - TIME: 613.2422159 s

method {:test} Test24() {
expect |"aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"| == |"aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n", "aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"| ==> "aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"[n] == "aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"[n] || "aaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}\U{0008}aa\U{0006}a\n"[n] == '?';
}
method {:test} Test25() {
expect |"aaa\U{0002}aaaaaaaaaa\U{0008}aaaa\U{000C}"| == |"aaa\0aaaaaaa\U{0004}a\U{0006}aaaaa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{0002}aaaaaaaaaa\U{0008}aaaa\U{000C}", "aaa\0aaaaaaa\U{0004}a\U{0006}aaaaa\n");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{0002}aaaaaaaaaa\U{0008}aaaa\U{000C}"| ==> "aaa\U{0002}aaaaaaaaaa\U{0008}aaaa\U{000C}"[n] == "aaa\0aaaaaaa\U{0004}a\U{0006}aaaaa\n"[n] || "aaa\0aaaaaaa\U{0004}a\U{0006}aaaaa\n"[n] == '?';
}
method {:test} Test26() {
expect |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| == |"\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aa\0aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aa\0aaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| ==> "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[n] == "\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aa\0aaaaa"[n] || "\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aa\0aaaaa"[n] == '?';
}

// REPEAT 9 - TIME: 828.1418782 s

method {:test} Test27() {
expect |"aaaaaaaaaa\0a\U{0004}\U{0002}"| == |"aaaaaaaaaa\0a\U{0004}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaa\0a\U{0004}\U{0002}", "aaaaaaaaaa\0a\U{0004}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaa\0a\U{0004}\U{0002}"| ==> "aaaaaaaaaa\0a\U{0004}\U{0002}"[n] == "aaaaaaaaaa\0a\U{0004}\U{0002}"[n] || "aaaaaaaaaa\0a\U{0004}\U{0002}"[n] == '?';
}
method {:test} Test28() {
expect |"aaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa\U{0004}"| == |"aaaaaaaaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa\U{0004}", "aaaaaaaaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa\U{0004}"| ==> "aaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa\U{0004}"[n] == "aaaaaaaaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}"[n] || "aaaaaaaaaaaaa\U{0002}a\U{0006}aaaaaaaaaa\U{0004}"[n] == '?';
}
method {:test} Test29() {
expect |"aaa\0aaaaaaaaaaaaaa\U{0002}\U{0004}a"| == |"aaa\U{0006}aaaaaaaaaaaaaa\U{0002}\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\0aaaaaaaaaaaaaa\U{0002}\U{0004}a", "aaa\U{0006}aaaaaaaaaaaaaa\U{0002}\U{0004}a");
expect r0 <==> forall n :: 0 <= n < |"aaa\0aaaaaaaaaaaaaa\U{0002}\U{0004}a"| ==> "aaa\0aaaaaaaaaaaaaa\U{0002}\U{0004}a"[n] == "aaa\U{0006}aaaaaaaaaaaaaa\U{0002}\U{0004}a"[n] || "aaa\U{0006}aaaaaaaaaaaaaa\U{0002}\U{0004}a"[n] == '?';
}

// REPEAT 10 - TIME: 1004.6822937 s
