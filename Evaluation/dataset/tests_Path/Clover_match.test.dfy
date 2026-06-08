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

// REPEAT 1 - TIME: 34.0667493 s

method {:test} Test3() {
expect |"aa"| == |"aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa", "aa");
expect r0 <==> forall n :: 0 <= n < |"aa"| ==> "aa"[n] == "aa"[n] || "aa"[n] == '?';
}
method {:test} Test4() {
expect |"\U{0004}\U{0002}"| == |"\U{0006}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\U{0002}", "\U{0006}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\U{0002}"| ==> "\U{0004}\U{0002}"[n] == "\U{0006}\0"[n] || "\U{0006}\0"[n] == '?';
}

// REPEAT 2 - TIME: 58.0452248 s

method {:test} Test6() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[n] == '?';
}
method {:test} Test7() {
expect |"\U{0008}\U{0002}\U{0006}"| == |"\n\0\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}\U{0002}\U{0006}", "\n\0\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}\U{0002}\U{0006}"| ==> "\U{0008}\U{0002}\U{0006}"[n] == "\n\0\U{0004}"[n] || "\n\0\U{0004}"[n] == '?';
}
method {:test} Test8() {
expect |"\naaaaaa\U{0006}aaaa\U{0002}aaaaa"| == |"\U{0008}\0aaaaaaaaaaaaaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naaaaaa\U{0006}aaaa\U{0002}aaaaa", "\U{0008}\0aaaaaaaaaaaaaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\naaaaaa\U{0006}aaaa\U{0002}aaaaa"| ==> "\naaaaaa\U{0006}aaaa\U{0002}aaaaa"[n] == "\U{0008}\0aaaaaaaaaaaaaaa\U{0004}"[n] || "\U{0008}\0aaaaaaaaaaaaaaa\U{0004}"[n] == '?';
}

// REPEAT 3 - TIME: 80.3357955 s

method {:test} Test9() {
expect |"\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"| == |"\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n", "\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"| ==> "\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"[n] == "\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"[n] || "\U{0002}a\0\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}\n"[n] == '?';
}
method {:test} Test10() {
expect |"\0aaaaaaaa\U{0006}aaaaaaaa\U{0008}"| == |"\U{0002}aa\U{0004}aaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaa\U{0006}aaaaaaaa\U{0008}", "\U{0002}aa\U{0004}aaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaa\U{0006}aaaaaaaa\U{0008}"| ==> "\0aaaaaaaa\U{0006}aaaaaaaa\U{0008}"[n] == "\U{0002}aa\U{0004}aaaaaaaaaaaaaaa"[n] || "\U{0002}aa\U{0004}aaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test11() {
expect |"\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{000C}"| == |"\U{0002}\0a\naaa\U{0008}aaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{000C}", "\U{0002}\0a\naaa\U{0008}aaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{000C}"| ==> "\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{000C}"[n] == "\U{0002}\0a\naaa\U{0008}aaaaaaaaaaa"[n] || "\U{0002}\0a\naaa\U{0008}aaaaaaaaaaa"[n] == '?';
}

// REPEAT 4 - TIME: 103.935197 s

method {:test} Test12() {
expect |"aaa\0aaaaaaaaaaaaaa\U{0004}a\U{0006}aa\U{0002}aaaaaaaaaaaaaa\U{0008}\n"| == |"aaa\0aaaaaaaaaaaaaa\U{0004}a\U{0006}aa\U{0002}aaaaaaaaaaaaaa\U{0008}\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\0aaaaaaaaaaaaaa\U{0004}a\U{0006}aa\U{0002}aaaaaaaaaaaaaa\U{0008}\n", "aaa\0aaaaaaaaaaaaaa\U{0004}a\U{0006}aa\U{0002}aaaaaaaaaaaaaa\U{0008}\n");
expect r0 <==> forall n :: 0 <= n < |"aaa\0aaaaaaaaaaaaaa\U{0004}a\U{0006}aa\U{0002}aaaaaaaaaaaaaa\U{0008}\n"| ==> "aaa\0aaaaaaaaaaaaaa\U{0004}a\U{0006}aa\U{0002}aaaaaaaaaaaaaa\U{0008}\n"[n] == "aaa\0aaaaaaaaaaaaaa\U{0004}a\U{0006}aa\U{0002}aaaaaaaaaaaaaa\U{0008}\n"[n] || "aaa\0aaaaaaaaaaaaaa\U{0004}a\U{0006}aa\U{0002}aaaaaaaaaaaaaa\U{0008}\n"[n] == '?';
}
method {:test} Test13() {
expect |"\U{0004}a\0a"| == |"\U{0004}a\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}a\0a", "\U{0004}a\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}a\0a"| ==> "\U{0004}a\0a"[n] == "\U{0004}a\U{0002}a"[n] || "\U{0004}a\U{0002}a"[n] == '?';
}
method {:test} Test14() {
expect |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| == |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| ==> "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"[n] == "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a"[n] || "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a"[n] == '?';
}

// REPEAT 5 - TIME: 118.5379057 s

method {:test} Test15() {
expect |"aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"| == |"aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n", "aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"| ==> "aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"[n] == "aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"[n] || "aaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\U{0006}aaaaaa\0a\U{0004}aaaa\n"[n] == '?';
}
method {:test} Test16() {
expect |"aa\0a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"| == |"aa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa", "aa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa");
expect r0 <==> forall n :: 0 <= n < |"aa\0a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"| ==> "aa\0a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] == "aa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] || "aa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] == '?';
}
method {:test} Test17() {
expect |"aa\0\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"| == |"aa\U{0002}\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa", "aa\U{0002}\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa");
expect r0 <==> forall n :: 0 <= n < |"aa\0\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"| ==> "aa\0\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] == "aa\U{0002}\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] || "aa\U{0002}\U{0004}aaaaaaaaaaaaaa\U{0008}aaaaaaaa\U{0006}aaaaaaaaaa\naa"[n] == '?';
}

// REPEAT 6 - TIME: 131.8944941 s

method {:test} Test18() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0"[n] == '?';
}
method {:test} Test19() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}aaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\0aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}aaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\0aaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}aaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}aaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\0aaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\0aaa"[n] == '?';
}

// REPEAT 7 - TIME: 145.4982664 s

method {:test} Test21() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0004}"[n] == '?';
}
method {:test} Test22() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}aaaaa\U{0004}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}aaaaa\U{0004}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}aaaaa\U{0004}aa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}aaaaa\U{0004}aa"[n] == '?';
}
method {:test} Test23() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa"[n] == '?';
}

// REPEAT 8 - TIME: 163.7045532 s

method {:test} Test24() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaa"[n] == '?';
}

// REPEAT 9 - TIME: 192.4779203 s

method {:test} Test27() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test28() {
expect |"aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 10 - TIME: 235.6115994 s
