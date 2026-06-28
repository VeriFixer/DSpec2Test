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
expect |"aaaaaaaa\0"| == |"aaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaa\0", "aaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaa\0"| ==> "aaaaaaaa\0"[n] == "aaaaaaaa\U{0002}"[n] || "aaaaaaaa\U{0002}"[n] == '?';
}

// REPEAT 1 - TIME: 3.4749657 s

method {:test} Test2() {
expect |"a"| == |"a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a", "a");
expect r0 <==> forall n :: 0 <= n < |"a"| ==> "a"[n] == "a"[n] || "a"[n] == '?';
}
method {:test} Test3() {
expect |"\U{0002}"| == |"\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}", "\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}"| ==> "\U{0002}"[n] == "\0"[n] || "\0"[n] == '?';
}

// REPEAT 2 - TIME: 5.0405564 s

method {:test} Test4() {
expect |"\U{0002}\0"| == |"\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0", "\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0"| ==> "\U{0002}\0"[n] == "\U{0002}\0"[n] || "\U{0002}\0"[n] == '?';
}
method {:test} Test5() {
expect |"a\U{0004}aaaaaaa\U{0002}"| == |"a\U{0006}aaaaa\0aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0004}aaaaaaa\U{0002}", "a\U{0006}aaaaa\0aa");
expect r0 <==> forall n :: 0 <= n < |"a\U{0004}aaaaaaa\U{0002}"| ==> "a\U{0004}aaaaaaa\U{0002}"[n] == "a\U{0006}aaaaa\0aa"[n] || "a\U{0006}aaaaa\0aa"[n] == '?';
}

// REPEAT 3 - TIME: 6.3681496 s

method {:test} Test6() {
expect |"\U{0003}aaa\U{0001}"| == |"??aa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0003}aaa\U{0001}", "??aa?");
expect r0 <==> forall n :: 0 <= n < |"\U{0003}aaa\U{0001}"| ==> "\U{0003}aaa\U{0001}"[n] == "??aa?"[n] || "??aa?"[n] == '?';
}
method {:test} Test7() {
expect |"\n\0\U{0004}aaaaaaaa"| == |"\U{0008}\U{0002}\U{0006}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\n\0\U{0004}aaaaaaaa", "\U{0008}\U{0002}\U{0006}aaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\n\0\U{0004}aaaaaaaa"| ==> "\n\0\U{0004}aaaaaaaa"[n] == "\U{0008}\U{0002}\U{0006}aaaaaaaa"[n] || "\U{0008}\U{0002}\U{0006}aaaaaaaa"[n] == '?';
}

// REPEAT 4 - TIME: 7.7885366 s

method {:test} Test8() {
expect |"aaaaaa\U{0001}aa\U{0003}a\U{0005}aaaaaaaaaaaa\U{0007}"| == |"?aa?a??aa?a?aaaaaaaaaaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaa\U{0001}aa\U{0003}a\U{0005}aaaaaaaaaaaa\U{0007}", "?aa?a??aa?a?aaaaaaaaaaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaa\U{0001}aa\U{0003}a\U{0005}aaaaaaaaaaaa\U{0007}"| ==> "aaaaaa\U{0001}aa\U{0003}a\U{0005}aaaaaaaaaaaa\U{0007}"[n] == "?aa?a??aa?a?aaaaaaaaaaaa?"[n] || "?aa?a??aa?a?aaaaaaaaaaaa?"[n] == '?';
}
method {:test} Test9() {
expect |"a\U{0004}\0"| == |"a\U{0006}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0004}\0", "a\U{0006}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0004}\0"| ==> "a\U{0004}\0"[n] == "a\U{0006}\U{0002}"[n] || "a\U{0006}\U{0002}"[n] == '?';
}

// REPEAT 5 - TIME: 9.0578891 s

method {:test} Test10() {
expect |"\0aaaaaaa"| == |"?a?aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaa", "?a?aaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaa"| ==> "\0aaaaaaa"[n] == "?a?aaaaa"[n] || "?a?aaaaa"[n] == '?';
}
method {:test} Test11() {
expect |"\na\U{0006}aa\U{000E}aa\0\U{0012}"| == |"\U{0014}a\U{0004}\U{000C}a\U{0010}aa\U{0002}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\na\U{0006}aa\U{000E}aa\0\U{0012}", "\U{0014}a\U{0004}\U{000C}a\U{0010}aa\U{0002}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\na\U{0006}aa\U{000E}aa\0\U{0012}"| ==> "\na\U{0006}aa\U{000E}aa\0\U{0012}"[n] == "\U{0014}a\U{0004}\U{000C}a\U{0010}aa\U{0002}\U{0008}"[n] || "\U{0014}a\U{0004}\U{000C}a\U{0010}aa\U{0002}\U{0008}"[n] == '?';
}

// REPEAT 6 - TIME: 10.6150492 s

method {:test} Test12() {
expect |"\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"| == |"\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}", "\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"| ==> "\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"[n] == "\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"[n] || "\0aaaaaaaa\U{000C}aa\U{0008}aa\U{0010}a\U{0006}\U{0002}a\naa\U{000E}\U{0012}\U{0004}"[n] == '?';
}
method {:test} Test13() {
expect |"aaaaaaaaaaaa\0aa\U{0010}aaaaaaa\U{000C}a\U{0012}"| == |"aaaaaaaaaaa\U{0008}\U{0002}aa\n\U{000E}aa\U{0004}aaa\U{0006}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaa\0aa\U{0010}aaaaaaa\U{000C}a\U{0012}", "aaaaaaaaaaa\U{0008}\U{0002}aa\n\U{000E}aa\U{0004}aaa\U{0006}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaa\0aa\U{0010}aaaaaaa\U{000C}a\U{0012}"| ==> "aaaaaaaaaaaa\0aa\U{0010}aaaaaaa\U{000C}a\U{0012}"[n] == "aaaaaaaaaaa\U{0008}\U{0002}aa\n\U{000E}aa\U{0004}aaa\U{0006}aa"[n] || "aaaaaaaaaaa\U{0008}\U{0002}aa\n\U{000E}aa\U{0004}aaa\U{0006}aa"[n] == '?';
}

// REPEAT 7 - TIME: 12.0677475 s

method {:test} Test14() {
expect |"aaaaaaa\0aaaaaaaa\U{0004}aaaaaaaaa\U{0002}"| == |"aaaaaaa?aaa?a?aa?a?aaaaaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\0aaaaaaaa\U{0004}aaaaaaaaa\U{0002}", "aaaaaaa?aaa?a?aa?a?aaaaaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\0aaaaaaaa\U{0004}aaaaaaaaa\U{0002}"| ==> "aaaaaaa\0aaaaaaaa\U{0004}aaaaaaaaa\U{0002}"[n] == "aaaaaaa?aaa?a?aa?a?aaaaaaa?"[n] || "aaaaaaa?aaa?a?aa?a?aaaaaaa?"[n] == '?';
}
method {:test} Test15() {
expect |"aaaaaaaaaaaaa\U{000C}aa\U{0008}aaaaaaa\0a\U{0010}a\U{0014}"| == |"aa\U{0004}aaaaaaaa\U{000E}aaaa\U{0006}aaaaaa\n\U{0002}\U{0012}\U{0018}a\U{0016}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaa\U{000C}aa\U{0008}aaaaaaa\0a\U{0010}a\U{0014}", "aa\U{0004}aaaaaaaa\U{000E}aaaa\U{0006}aaaaaa\n\U{0002}\U{0012}\U{0018}a\U{0016}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaa\U{000C}aa\U{0008}aaaaaaa\0a\U{0010}a\U{0014}"| ==> "aaaaaaaaaaaaa\U{000C}aa\U{0008}aaaaaaa\0a\U{0010}a\U{0014}"[n] == "aa\U{0004}aaaaaaaa\U{000E}aaaa\U{0006}aaaaaa\n\U{0002}\U{0012}\U{0018}a\U{0016}"[n] || "aa\U{0004}aaaaaaaa\U{000E}aaaa\U{0006}aaaaaa\n\U{0002}\U{0012}\U{0018}a\U{0016}"[n] == '?';
}

// REPEAT 8 - TIME: 13.3953457 s

method {:test} Test16() {
expect |"aaaaaaaaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaa\0"| == |"aaaaaa?aa?a?aa?a?a?aaaaa?aaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaa\0", "aaaaaa?aa?a?aa?a?a?aaaaa?aaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaa\0"[n] == "aaaaaa?aa?a?aa?a?a?aaaaa?aaaa?"[n] || "aaaaaa?aa?a?aa?a?a?aaaaa?aaaa?"[n] == '?';
}
method {:test} Test17() {
expect |"\naa\0a\U{0006}"| == |"\U{0008}aa\U{0002}a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naa\0a\U{0006}", "\U{0008}aa\U{0002}a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\naa\0a\U{0006}"| ==> "\naa\0a\U{0006}"[n] == "\U{0008}aa\U{0002}a\U{0004}"[n] || "\U{0008}aa\U{0002}a\U{0004}"[n] == '?';
}

// REPEAT 9 - TIME: 14.8719907 s

method {:test} Test18() {
expect |"\U{0002}a\0a"| == |"\U{0002}a\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}a\0a", "\U{0002}a\0a");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}a\0a"| ==> "\U{0002}a\0a"[n] == "\U{0002}a\0a"[n] || "\U{0002}a\0a"[n] == '?';
}
method {:test} Test19() {
expect |"\U{0006}aaaaaaa\0aaaaaaaaaaaaaaaaaaaaa"| == |"\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}aaaaaaa\0aaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}aaaaaaa\0aaaaaaaaaaaaaaaaaaaaa"| ==> "\U{0006}aaaaaaa\0aaaaaaaaaaaaaaaaaaaaa"[n] == "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaa"[n] || "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 10 - TIME: 16.2968812 s
