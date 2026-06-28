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
    if s[i] != p[i] || p[i] != '?' {
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

// REPEAT 1 - TIME: 2.6524021 s

method {:test} Test3() {
expect |"a\0"| == |"a\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0", "a\0");
expect r0 <==> forall n :: 0 <= n < |"a\0"| ==> "a\0"[n] == "a\0"[n] || "a\0"[n] == '?';
}
method {:test} Test4() {
expect |"\na\U{0002}aaaaa\U{0004}"| == |"\U{0006}\0aaaaaa\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\na\U{0002}aaaaa\U{0004}", "\U{0006}\0aaaaaa\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\na\U{0002}aaaaa\U{0004}"| ==> "\na\U{0002}aaaaa\U{0004}"[n] == "\U{0006}\0aaaaaa\U{0008}"[n] || "\U{0006}\0aaaaaa\U{0008}"[n] == '?';
}
method {:test} Test5() {
expect |"\0a"| == |"\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0a", "\0a");
expect r0 <==> forall n :: 0 <= n < |"\0a"| ==> "\0a"[n] == "\0a"[n] || "\0a"[n] == '?';
}

// REPEAT 2 - TIME: 4.4192013 s

method {:test} Test6() {
expect |"\U{0002}\0a"| == |"\U{0002}\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0a", "\U{0002}\0a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0a"| ==> "\U{0002}\0a"[n] == "\U{0002}\0a"[n] || "\U{0002}\0a"[n] == '?';
}
method {:test} Test7() {
expect |"\0aa"| == |"\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa", "\U{0002}aa");
expect r0 <==> forall n :: 0 <= n < |"\0aa"| ==> "\0aa"[n] == "\U{0002}aa"[n] || "\U{0002}aa"[n] == '?';
}
method {:test} Test8() {
expect |"\0a"| == |"\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0a", "\0a");
expect r0 <==> forall n :: 0 <= n < |"\0a"| ==> "\0a"[n] == "\0a"[n] || "\0a"[n] == '?';
}

// REPEAT 3 - TIME: 6.2015728 s

method {:test} Test9() {
expect |"a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"| == |"a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}", "a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"| ==> "a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"[n] == "a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"[n] || "a\U{0004}a\U{0002}a\0aaa\U{0006}\n\U{0008}"[n] == '?';
}
method {:test} Test10() {
expect |"\n\0aaa\U{0002}aaa\U{0004}\U{0006}"| == |"\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\n\0aaa\U{0002}aaa\U{0004}\U{0006}", "\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\n\0aaa\U{0002}aaa\U{0004}\U{0006}"| ==> "\n\0aaa\U{0002}aaa\U{0004}\U{0006}"[n] == "\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"[n] || "\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"[n] == '?';
}
method {:test} Test11() {
expect |"\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"| == |"\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na", "\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na");
expect r0 <==> forall n :: 0 <= n < |"\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"| ==> "\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"[n] == "\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"[n] || "\0aa\U{0008}aaaaa\U{0004}aaaaaaaa\U{0002}aaaaaaa\U{0006}\na"[n] == '?';
}

// REPEAT 4 - TIME: 7.8522038 s

method {:test} Test12() {
expect |"\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"| == |"\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n", "\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"| ==> "\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"[n] == "\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"[n] || "\U{0002}\0aaaaaaa\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\U{0008}\n"[n] == '?';
}
method {:test} Test13() {
expect |"\U{0004}aaaa\U{0002}aaaaa"| == |"\U{0004}aaaa\0aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaa\U{0002}aaaaa", "\U{0004}aaaa\0aaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaa\U{0002}aaaaa"| ==> "\U{0004}aaaa\U{0002}aaaaa"[n] == "\U{0004}aaaa\0aaaaa"[n] || "\U{0004}aaaa\0aaaaa"[n] == '?';
}
method {:test} Test14() {
expect |"\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"| == |"\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}", "\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}");
expect r0 <==> forall n :: 0 <= n < |"\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"| ==> "\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"[n] == "\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"[n] || "\0aa\U{0008}aaaaa\U{0002}a\U{0004}aaa\U{000E}\U{0006}aaa\na\U{000C}aaaa\U{0010}a\U{0012}"[n] == '?';
}

// REPEAT 5 - TIME: 9.0560942 s

method {:test} Test15() {
expect |"\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"| == |"\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}", "\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"| ==> "\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"[n] == "\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"[n] || "\naa\0aaaaaaaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}\U{0008}"[n] == '?';
}
method {:test} Test16() {
expect |"\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0008}aaaaaa\U{0002}a"| == |"\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0006}aaaaaa\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0008}aaaaaa\U{0002}a", "\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0006}aaaaaa\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0008}aaaaaa\U{0002}a"| ==> "\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0008}aaaaaa\U{0002}a"[n] == "\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0006}aaaaaa\U{0002}a"[n] || "\U{0004}aaaaaaaaaaaaaaaaaa\0a\U{0006}aaaaaa\U{0002}a"[n] == '?';
}
method {:test} Test17() {
expect |"aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"| == |"aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a", "aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"| ==> "aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"[n] == "aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"[n] || "aaa\U{0004}aaaaa\0a\U{0008}aaaaa\naaaaa\U{0002}\U{0006}\U{000C}a\U{000E}a"[n] == '?';
}

// REPEAT 6 - TIME: 10.3683282 s

method {:test} Test18() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test19() {
expect |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaa"[n] || "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test20() {
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaa"[n] || "\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 7 - TIME: 11.9467539 s

method {:test} Test21() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test22() {
expect |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"| == |"aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaa\0aa", "aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] == "aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[n] || "aaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[n] == '?';
}
method {:test} Test23() {
expect |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"| == |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaa\0aa", "aaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaa\0aa"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] == "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] || "aaaaaaaaaaaaaaaaaaaaaaa\0aa"[n] == '?';
}

// REPEAT 8 - TIME: 13.4887155 s

method {:test} Test24() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaa\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaa\0"[n] || "aaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaaaaaaaaaa\0aaaaaaaaaaa"| == |"aaaaaaaaaaaaa\U{0002}aaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\0aaaaaaaaaaa", "aaaaaaaaaaaaa\U{0002}aaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\0aaaaaaaaaaa"| ==> "aaaaaaaaaaaaa\0aaaaaaaaaaa"[n] == "aaaaaaaaaaaaa\U{0002}aaaaaaaaaaa"[n] || "aaaaaaaaaaaaa\U{0002}aaaaaaaaaaa"[n] == '?';
}
method {:test} Test26() {
expect |"aaaaaaaaaa\0aaaaaaa\U{0006}aaaaaa"| == |"aaaaaaaaaa\0\U{0002}aaaaaa\U{0004}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaa\0aaaaaaa\U{0006}aaaaaa", "aaaaaaaaaa\0\U{0002}aaaaaa\U{0004}aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaa\0aaaaaaa\U{0006}aaaaaa"| ==> "aaaaaaaaaa\0aaaaaaa\U{0006}aaaaaa"[n] == "aaaaaaaaaa\0\U{0002}aaaaaa\U{0004}aaaaaa"[n] || "aaaaaaaaaa\0\U{0002}aaaaaa\U{0004}aaaaaa"[n] == '?';
}

// REPEAT 9 - TIME: 15.4472775 s

method {:test} Test27() {
expect |"aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"| == |"aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}", "aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"| ==> "aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"[n] == "aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"[n] || "aaaaaaaaaaaaa\0aaaaaaaaa\U{0002}"[n] == '?';
}
method {:test} Test28() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaa"| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaaaaaaaaaaaaaaaaa"| ==> "\0aaaaaaaaaaaaaaaaaaaaaaa"[n] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa"[n] || "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test29() {
expect |"aaaaaaaaaaaaaaaaaaaaaa\0a"| == |"aaaaaaaaaaaaaaaaaaaaaa\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaa\0a", "aaaaaaaaaaaaaaaaaaaaaa\0a");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaa\0a"| ==> "aaaaaaaaaaaaaaaaaaaaaa\0a"[n] == "aaaaaaaaaaaaaaaaaaaaaa\0a"[n] || "aaaaaaaaaaaaaaaaaaaaaa\0a"[n] == '?';
}

// REPEAT 10 - TIME: 17.331566 s
