// Clover_match.dfy

method {:testEntry} Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
  var i := 0;
  while true
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

// REPEAT 1 - TIME: 14.4748643 s

method {:test} Test20() {
expect |"\U{0001}aa"| == |"?a?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0001}aa", "?a?");
expect r0 <==> forall n :: 0 <= n < |"\U{0001}aa"| ==> "\U{0001}aa"[n] == "?a?"[n] || "?a?"[n] == '?';
}
method {:test} Test21() {
expect |"\U{0004}\U{0008}aaaa"| == |"\U{0006}\n\0aa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\U{0008}aaaa", "\U{0006}\n\0aa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\U{0008}aaaa"| ==> "\U{0004}\U{0008}aaaa"[n] == "\U{0006}\n\0aa\U{0002}"[n] || "\U{0006}\n\0aa\U{0002}"[n] == '?';
}

// REPEAT 2 - TIME: 15.938686 s

method {:test} Test22() {
expect |"\U{0003}a\U{0001}aaaa"| == |"?????a?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0003}a\U{0001}aaaa", "?????a?");
expect r0 <==> forall n :: 0 <= n < |"\U{0003}a\U{0001}aaaa"| ==> "\U{0003}a\U{0001}aaaa"[n] == "?????a?"[n] || "?????a?"[n] == '?';
}
method {:test} Test23() {
expect |"\U{0008}a\U{0002}\U{0006}"| == |"\na\U{0004}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}a\U{0002}\U{0006}", "\na\U{0004}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}a\U{0002}\U{0006}"| ==> "\U{0008}a\U{0002}\U{0006}"[n] == "\na\U{0004}\0"[n] || "\na\U{0004}\0"[n] == '?';
}

// REPEAT 3 - TIME: 17.3578312 s

method {:test} Test24() {
expect |"\U{0004}\U{0008}\U{0002}\0\U{0006}"| == |"?\U{0008}???"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\U{0008}\U{0002}\0\U{0006}", "?\U{0008}???");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\U{0008}\U{0002}\0\U{0006}"| ==> "\U{0004}\U{0008}\U{0002}\0\U{0006}"[n] == "?\U{0008}???"[n] || "?\U{0008}???"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaa\U{0004}\0\U{0008}"| == |"aaaaaa\U{0002}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\U{0004}\0\U{0008}", "aaaaaa\U{0002}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\U{0004}\0\U{0008}"| ==> "aaaaa\U{0004}\0\U{0008}"[n] == "aaaaaa\U{0002}\U{0006}"[n] || "aaaaaa\U{0002}\U{0006}"[n] == '?';
}

// REPEAT 4 - TIME: 18.7600349 s

method {:test} Test26() {
expect |"\U{0006}aa\U{0004}\U{0002}\0"| == |"\U{0006}aa\U{0004}\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}aa\U{0004}\U{0002}\0", "\U{0006}aa\U{0004}\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}aa\U{0004}\U{0002}\0"| ==> "\U{0006}aa\U{0004}\U{0002}\0"[n] == "\U{0006}aa\U{0004}\U{0002}\0"[n] || "\U{0006}aa\U{0004}\U{0002}\0"[n] == '?';
}
method {:test} Test27() {
expect |"\U{0006}aaaa\0a\U{0008}\U{0012}\U{000E}"| == |"a\U{0004}\U{0002}aa\n\U{000C}\U{0010}\U{0014}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0006}aaaa\0a\U{0008}\U{0012}\U{000E}", "a\U{0004}\U{0002}aa\n\U{000C}\U{0010}\U{0014}a");
expect r0 <==> forall n :: 0 <= n < |"\U{0006}aaaa\0a\U{0008}\U{0012}\U{000E}"| ==> "\U{0006}aaaa\0a\U{0008}\U{0012}\U{000E}"[n] == "a\U{0004}\U{0002}aa\n\U{000C}\U{0010}\U{0014}a"[n] || "a\U{0004}\U{0002}aa\n\U{000C}\U{0010}\U{0014}a"[n] == '?';
}

// REPEAT 5 - TIME: 20.0711421 s

method {:test} Test28() {
expect |"aaaaaaa\U{0002}a\U{0004}\0"| == |"aaaaaaa\U{0002}a\U{0004}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\U{0002}a\U{0004}\0", "aaaaaaa\U{0002}a\U{0004}\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\U{0002}a\U{0004}\0"| ==> "aaaaaaa\U{0002}a\U{0004}\0"[n] == "aaaaaaa\U{0002}a\U{0004}\0"[n] || "aaaaaaa\U{0002}a\U{0004}\0"[n] == '?';
}
method {:test} Test29() {
expect |"aaa\U{0004}\n\U{000C}aaa\U{0012}\U{000E}"| == |"aa\U{0002}aa\0\U{0008}\U{0010}aa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{0004}\n\U{000C}aaa\U{0012}\U{000E}", "aa\U{0002}aa\0\U{0008}\U{0010}aa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{0004}\n\U{000C}aaa\U{0012}\U{000E}"| ==> "aaa\U{0004}\n\U{000C}aaa\U{0012}\U{000E}"[n] == "aa\U{0002}aa\0\U{0008}\U{0010}aa\U{0006}"[n] || "aa\U{0002}aa\0\U{0008}\U{0010}aa\U{0006}"[n] == '?';
}

// REPEAT 6 - TIME: 21.2803447 s

method {:test} Test30() {
expect |"aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"| == |"aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}", "aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"| ==> "aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"[n] == "aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"[n] || "aaaaa\0aaa\U{0004}\U{0006}\U{0008}\U{0012}aaa\U{000E}aa\U{0002}aaaaa\naa\U{000C}\U{0010}"[n] == '?';
}
method {:test} Test31() {
expect |"aa\0aa\U{0004}\U{0006}aa\U{000E}\U{000C}\U{0010}"| == |"aa\U{0002}aaaaaa\n\U{0008}\U{0012}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aa\0aa\U{0004}\U{0006}aa\U{000E}\U{000C}\U{0010}", "aa\U{0002}aaaaaa\n\U{0008}\U{0012}");
expect r0 <==> forall n :: 0 <= n < |"aa\0aa\U{0004}\U{0006}aa\U{000E}\U{000C}\U{0010}"| ==> "aa\0aa\U{0004}\U{0006}aa\U{000E}\U{000C}\U{0010}"[n] == "aa\U{0002}aaaaaa\n\U{0008}\U{0012}"[n] || "aa\U{0002}aaaaaa\n\U{0008}\U{0012}"[n] == '?';
}

// REPEAT 7 - TIME: 22.507467 s

method {:test} Test32() {
expect |"\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"| == |"\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}", "\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"| ==> "\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"[n] == "\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"[n] || "\naa\0aaa\U{0004}a\U{0006}a\U{0002}\U{0008}"[n] == '?';
}
method {:test} Test33() {
expect |"aaaaaaa\U{0008}\U{0014}\U{0016}\U{000C}\U{0010}\0"| == |"aa\U{0004}aa\U{000E}\n\U{0012}aaa\U{0006}\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaa\U{0008}\U{0014}\U{0016}\U{000C}\U{0010}\0", "aa\U{0004}aa\U{000E}\n\U{0012}aaa\U{0006}\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaa\U{0008}\U{0014}\U{0016}\U{000C}\U{0010}\0"| ==> "aaaaaaa\U{0008}\U{0014}\U{0016}\U{000C}\U{0010}\0"[n] == "aa\U{0004}aa\U{000E}\n\U{0012}aaa\U{0006}\U{0002}"[n] || "aa\U{0004}aa\U{000E}\n\U{0012}aaa\U{0006}\U{0002}"[n] == '?';
}

// REPEAT 8 - TIME: 23.8325839 s

method {:test} Test34() {
expect |"\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"| == |"\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}", "\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"| ==> "\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"[n] == "\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"[n] || "\naaaa\0a\U{0004}a\U{0002}aaa\U{0008}aaaaaaaa\U{0006}"[n] == '?';
}
method {:test} Test35() {
expect |"\U{0014}aaaaaa\U{0006}aa\0a\U{000C}\U{0008}"| == |"\U{0012}aaaaaa\U{0004}aa\U{0002}\n\U{000E}\U{0010}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0014}aaaaaa\U{0006}aa\0a\U{000C}\U{0008}", "\U{0012}aaaaaa\U{0004}aa\U{0002}\n\U{000E}\U{0010}");
expect r0 <==> forall n :: 0 <= n < |"\U{0014}aaaaaa\U{0006}aa\0a\U{000C}\U{0008}"| ==> "\U{0014}aaaaaa\U{0006}aa\0a\U{000C}\U{0008}"[n] == "\U{0012}aaaaaa\U{0004}aa\U{0002}\n\U{000E}\U{0010}"[n] || "\U{0012}aaaaaa\U{0004}aa\U{0002}\n\U{000E}\U{0010}"[n] == '?';
}

// REPEAT 9 - TIME: 25.2364732 s

method {:test} Test36() {
expect |"aaaaaaaaaaaa\U{0003}a\U{0001}"| == |"?aaaaaaa?aaa???"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaa\U{0003}a\U{0001}", "?aaaaaaa?aaa???");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaa\U{0003}a\U{0001}"| ==> "aaaaaaaaaaaa\U{0003}a\U{0001}"[n] == "?aaaaaaa?aaa???"[n] || "?aaaaaaa?aaa???"[n] == '?';
}
method {:test} Test37() {
expect |"\U{0012}aaaaaaaa\0a\U{0008}aaa\U{000C}aaa\U{0006}aaaa"| == |"\U{0010}aaaaaaaa\U{0002}aaa\U{000E}\naa\U{0004}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0012}aaaaaaaa\0a\U{0008}aaa\U{000C}aaa\U{0006}aaaa", "\U{0010}aaaaaaaa\U{0002}aaa\U{000E}\naa\U{0004}aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0012}aaaaaaaa\0a\U{0008}aaa\U{000C}aaa\U{0006}aaaa"| ==> "\U{0012}aaaaaaaa\0a\U{0008}aaa\U{000C}aaa\U{0006}aaaa"[n] == "\U{0010}aaaaaaaa\U{0002}aaa\U{000E}\naa\U{0004}aaaaaa"[n] || "\U{0010}aaaaaaaa\U{0002}aaa\U{000E}\naa\U{0004}aaaaaa"[n] == '?';
}

// REPEAT 10 - TIME: 26.9456509 s
