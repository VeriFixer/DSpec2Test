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
expect |""| == |""|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("", "");
expect r0 <==> forall n :: 0 <= n < |""| ==> ""[n] == ""[n] || ""[n] == '?';
}
method {:test} Test2() {
expect |"a"| == |"a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a", "a");
expect r0 <==> forall n :: 0 <= n < |"a"| ==> "a"[n] == "a"[n] || "a"[n] == '?';
}
method {:test} Test3() {
expect |"aa"| == |"aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa", "aa");
expect r0 <==> forall n :: 0 <= n < |"aa"| ==> "aa"[n] == "aa"[n] || "aa"[n] == '?';
}
method {:test} Test11() {
expect |"aaaaaaaa\0"| == |"aaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaa\0", "aaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaa\0"| ==> "aaaaaaaa\0"[n] == "aaaaaaaa\U{0002}"[n] || "aaaaaaaa\U{0002}"[n] == '?';
}
method {:test} Test12() {
expect |"\0"| == |"\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0", "\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\0"| ==> "\0"[n] == "\U{0002}"[n] || "\U{0002}"[n] == '?';
}
method {:test} Test13() {
expect |"\0a"| == |"\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0a", "\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"\0a"| ==> "\0a"[n] == "\U{0002}a"[n] || "\U{0002}a"[n] == '?';
}

// REPEAT 1 - TIME: 12.4425617 s

method {:test} Test20() {
expect |"a\0a"| == |"a\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0a", "a\0a");
expect r0 <==> forall n :: 0 <= n < |"a\0a"| ==> "a\0a"[n] == "a\0a"[n] || "a\0a"[n] == '?';
}
method {:test} Test21() {
expect |"\U{0008}\U{0002}aa\U{0006}a\n"| == |"a\0aaaa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}\U{0002}aa\U{0006}a\n", "a\0aaaa\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}\U{0002}aa\U{0006}a\n"| ==> "\U{0008}\U{0002}aa\U{0006}a\n"[n] == "a\0aaaa\U{0004}"[n] || "a\0aaaa\U{0004}"[n] == '?';
}

// REPEAT 2 - TIME: 13.5034956 s

method {:test} Test22() {
expect |"\U{0001}aa"| == |"?a?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}aa", "?a?");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}aa"| ==> "\U{0001}aa"[n] == "?a?"[n] || "?a?"[n] == '?';
}
method {:test} Test23() {
expect |"aa\0\U{0004}"| == |"a\U{0002}\U{0006}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0\U{0004}", "a\U{0002}\U{0006}a");
expect r0 <==> forall n :: 0 <= n < |"aa\0\U{0004}"| ==> "aa\0\U{0004}"[n] == "a\U{0002}\U{0006}a"[n] || "a\U{0002}\U{0006}a"[n] == '?';
}

// REPEAT 3 - TIME: 14.4492431 s

method {:test} Test24() {
expect |"\0aaa\U{0002}"| == |"\0aaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaa\U{0002}", "\0aaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\0aaa\U{0002}"| ==> "\0aaa\U{0002}"[n] == "\0aaa\U{0002}"[n] || "\0aaa\U{0002}"[n] == '?';
}
method {:test} Test25() {
expect |"aaa\U{0006}a\n\0\U{000C}"| == |"\U{0002}aa\U{0004}aa\U{0008}\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{0006}a\n\0\U{000C}", "\U{0002}aa\U{0004}aa\U{0008}\U{000E}");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{0006}a\n\0\U{000C}"| ==> "aaa\U{0006}a\n\0\U{000C}"[n] == "\U{0002}aa\U{0004}aa\U{0008}\U{000E}"[n] || "\U{0002}aa\U{0004}aa\U{0008}\U{000E}"[n] == '?';
}

// REPEAT 4 - TIME: 15.4954482 s

method {:test} Test26() {
expect |"\U{0004}aa\0aaa\U{0002}aa"| == |"\U{0004}aa\0aaa\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aa\0aaa\U{0002}aa", "\U{0004}aa\0aaa\U{0002}aa");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aa\0aaa\U{0002}aa"| ==> "\U{0004}aa\0aaa\U{0002}aa"[n] == "\U{0004}aa\0aaa\U{0002}aa"[n] || "\U{0004}aa\0aaa\U{0002}aa"[n] == '?';
}
method {:test} Test27() {
expect |"\U{0008}a\U{0004}a"| == |"\U{0006}a\0\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}a\U{0004}a", "\U{0006}a\0\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}a\U{0004}a"| ==> "\U{0008}a\U{0004}a"[n] == "\U{0006}a\0\U{0002}"[n] || "\U{0006}a\0\U{0002}"[n] == '?';
}

// REPEAT 5 - TIME: 16.7462037 s

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

// REPEAT 6 - TIME: 18.032747 s

method {:test} Test30() {
expect |"aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"| == |"aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}", "aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"| ==> "aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"[n] == "aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"[n] || "aa\0a\U{0004}\U{0008}a\U{000E}a\U{000C}\naaaaa\U{0012}aaa\U{0010}aaaa\U{0006}\U{0002}"[n] == '?';
}
method {:test} Test31() {
expect |"aaaaaaa\U{0012}\0\U{000C}aaaaaaaaa\U{0006}\U{0010}aaaaaaaa\U{0016}"| == |"aaa\na\U{000E}\U{0008}a\U{0002}aaaaaaaaaaaaaaa\U{0004}aaaa\U{0014}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\U{0012}\0\U{000C}aaaaaaaaa\U{0006}\U{0010}aaaaaaaa\U{0016}", "aaa\na\U{000E}\U{0008}a\U{0002}aaaaaaaaaaaaaaa\U{0004}aaaa\U{0014}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\U{0012}\0\U{000C}aaaaaaaaa\U{0006}\U{0010}aaaaaaaa\U{0016}"| ==> "aaaaaaa\U{0012}\0\U{000C}aaaaaaaaa\U{0006}\U{0010}aaaaaaaa\U{0016}"[n] == "aaa\na\U{000E}\U{0008}a\U{0002}aaaaaaaaaaaaaaa\U{0004}aaaa\U{0014}"[n] || "aaa\na\U{000E}\U{0008}a\U{0002}aaaaaaaaaaaaaaa\U{0004}aaaa\U{0014}"[n] == '?';
}

// REPEAT 7 - TIME: 19.1727847 s

method {:test} Test32() {
expect |"\U{0001}aaaaaa"| == |"?aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}aaaaaa", "?aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}aaaaaa"| ==> "\U{0001}aaaaaa"[n] == "?aaaaaa"[n] || "?aaaaaa"[n] == '?';
}
method {:test} Test33() {
expect |"aaaaaaaaa\U{0010}\0\U{0006}aaaaaaaaaaaaa\U{000E}aa"| == |"a\U{0008}a\U{0004}aaaaaa\U{0002}aaaaaaa\U{000C}aa\naaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaa\U{0010}\0\U{0006}aaaaaaaaaaaaa\U{000E}aa", "a\U{0008}a\U{0004}aaaaaa\U{0002}aaaaaaa\U{000C}aa\naaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaa\U{0010}\0\U{0006}aaaaaaaaaaaaa\U{000E}aa"| ==> "aaaaaaaaa\U{0010}\0\U{0006}aaaaaaaaaaaaa\U{000E}aa"[n] == "a\U{0008}a\U{0004}aaaaaa\U{0002}aaaaaaa\U{000C}aa\naaaaaa"[n] || "a\U{0008}a\U{0004}aaaaaa\U{0002}aaaaaaa\U{000C}aa\naaaaaa"[n] == '?';
}

// REPEAT 8 - TIME: 20.2897273 s

method {:test} Test34() {
expect |"\U{0007}aaaaaa\U{0003}aaaaaaaaaaa\U{0005}aaaaaaa\U{0001}"| == |"?aaaaaa?aaa?aaaaaaa?aaaa?aa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0007}aaaaaa\U{0003}aaaaaaaaaaa\U{0005}aaaaaaa\U{0001}", "?aaaaaa?aaa?aaaaaaa?aaaa?aa?");
expect r0 <==> forall n :: 0 <= n < |"\U{0007}aaaaaa\U{0003}aaaaaaaaaaa\U{0005}aaaaaaa\U{0001}"| ==> "\U{0007}aaaaaa\U{0003}aaaaaaaaaaa\U{0005}aaaaaaa\U{0001}"[n] == "?aaaaaa?aaa?aaaaaaa?aaaa?aa?"[n] || "?aaaaaa?aaa?aaaaaaa?aaaa?aa?"[n] == '?';
}
method {:test} Test35() {
expect |"aaaaa\0\U{0004}aa\U{0008}\n"| == |"\U{000C}aaaa\U{0002}aaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0\U{0004}aa\U{0008}\n", "\U{000C}aaaa\U{0002}aaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0\U{0004}aa\U{0008}\n"| ==> "aaaaa\0\U{0004}aa\U{0008}\n"[n] == "\U{000C}aaaa\U{0002}aaaa\U{0006}"[n] || "\U{000C}aaaa\U{0002}aaaa\U{0006}"[n] == '?';
}

// REPEAT 9 - TIME: 21.6514102 s

method {:test} Test36() {
expect |"\U{0004}aaaaaa\U{0002}aa\0a"| == |"\U{0004}aaaaaa\U{0002}aa\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aaaaaa\U{0002}aa\0a", "\U{0004}aaaaaa\U{0002}aa\0a");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aaaaaa\U{0002}aa\0a"| ==> "\U{0004}aaaaaa\U{0002}aa\0a"[n] == "\U{0004}aaaaaa\U{0002}aa\0a"[n] || "\U{0004}aaaaaa\U{0002}aa\0a"[n] == '?';
}
method {:test} Test37() {
expect |"\U{0008}a\0aaaaaaaa\U{0004}"| == |"\na\U{0002}aaaaaaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}a\0aaaaaaaa\U{0004}", "\na\U{0002}aaaaaaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}a\0aaaaaaaa\U{0004}"| ==> "\U{0008}a\0aaaaaaaa\U{0004}"[n] == "\na\U{0002}aaaaaaaa\U{0006}"[n] || "\na\U{0002}aaaaaaaa\U{0006}"[n] == '?';
}

// REPEAT 10 - TIME: 23.0458732 s
