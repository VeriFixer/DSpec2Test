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
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[n] == '?';
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

// REPEAT 1 - TIME: 12.2628019 s

method {:test} Test20() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| == |"?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}", "?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[n] == "?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?"[n] || "?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?"[n] == '?';
}
method {:test} Test21() {
expect |"\U{0008}\U{0004}\0"| == |"\n\U{0002}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}\U{0004}\0", "\n\U{0002}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}\U{0004}\0"| ==> "\U{0008}\U{0004}\0"[n] == "\n\U{0002}\U{0006}"[n] || "\n\U{0002}\U{0006}"[n] == '?';
}

// REPEAT 2 - TIME: 13.5540392 s

method {:test} Test22() {
expect |"\U{0004}aa\0aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"| == |"??a?aaa?aaaaaaaaaaaaaaaaaaaaaaaa?a?a?aa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aa\0aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "??a?aaa?aaaaaaaaaaaaaaaaaaaaaaaa?a?a?aa?");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aa\0aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"| ==> "\U{0004}aa\0aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[n] == "??a?aaa?aaaaaaaaaaaaaaaaaaaaaaaa?a?a?aa?"[n] || "??a?aaa?aaaaaaaaaaaaaaaaaaaaaaaa?a?a?aa?"[n] == '?';
}
method {:test} Test23() {
expect |"\na\U{0002}\U{0006}"| == |"\U{0008}a\U{0004}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\na\U{0002}\U{0006}", "\U{0008}a\U{0004}\0");
expect r0 <==> forall n :: 0 <= n < |"\na\U{0002}\U{0006}"| ==> "\na\U{0002}\U{0006}"[n] == "\U{0008}a\U{0004}\0"[n] || "\U{0008}a\U{0004}\0"[n] == '?';
}

// REPEAT 3 - TIME: 14.9577855 s

method {:test} Test24() {
expect |"aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"| == |"aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n", "aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"| ==> "aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"[n] == "aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"[n] || "aaaaaaaaaa\0\U{0004}\U{0008}aaaaaaaaa\U{0006}aaaa\U{0002}aaaa\n"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{000E}"| == |"aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}aaaaa\0\n\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{000E}", "aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}aaaaa\0\n\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{000E}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{000E}"[n] == "aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}aaaaa\0\n\U{000C}"[n] || "aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0006}aaaaa\0\n\U{000C}"[n] == '?';
}

// REPEAT 4 - TIME: 16.2720935 s

method {:test} Test26() {
expect |"\0aaa\U{0002}"| == |"\0aa??"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaa\U{0002}", "\0aa??");
expect r0 <==> forall n :: 0 <= n < |"\0aaa\U{0002}"| ==> "\0aaa\U{0002}"[n] == "\0aa??"[n] || "\0aa??"[n] == '?';
}
method {:test} Test27() {
expect |"aaaaa\U{0014}aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaa\0\U{000E}\U{0018}a"| == |"aaaaaaaaaaa\U{0010}\U{000C}aaaa\naaaaa\U{0008}aa\U{0012}aaaaa\U{0016}aaaaa\U{0002}\U{001A}a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\U{0014}aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaa\0\U{000E}\U{0018}a", "aaaaaaaaaaa\U{0010}\U{000C}aaaa\naaaaa\U{0008}aa\U{0012}aaaaa\U{0016}aaaaa\U{0002}\U{001A}a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\U{0014}aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaa\0\U{000E}\U{0018}a"| ==> "aaaaa\U{0014}aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaa\0\U{000E}\U{0018}a"[n] == "aaaaaaaaaaa\U{0010}\U{000C}aaaa\naaaaa\U{0008}aa\U{0012}aaaaa\U{0016}aaaaa\U{0002}\U{001A}a\U{0004}"[n] || "aaaaaaaaaaa\U{0010}\U{000C}aaaa\naaaaa\U{0008}aa\U{0012}aaaaa\U{0016}aaaaa\U{0002}\U{001A}a\U{0004}"[n] == '?';
}

// REPEAT 5 - TIME: 17.8024346 s

method {:test} Test28() {
expect |"aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"| == |"aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}", "aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"| ==> "aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"[n] == "aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"[n] || "aaaaa\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaa\U{0008}aaaaa\0a\na\U{000C}"[n] == '?';
}
method {:test} Test29() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaa\0a\U{0010}\U{0006}\U{000E}"| == |"aaaaaaaaaaaaa\U{0008}\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0012}aa\n"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaa\0a\U{0010}\U{0006}\U{000E}", "aaaaaaaaaaaaa\U{0008}\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0012}aa\n");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaa\0a\U{0010}\U{0006}\U{000E}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaa\0a\U{0010}\U{0006}\U{000E}"[n] == "aaaaaaaaaaaaa\U{0008}\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0012}aa\n"[n] || "aaaaaaaaaaaaa\U{0008}\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0012}aa\n"[n] == '?';
}

// REPEAT 6 - TIME: 19.1398171 s

method {:test} Test30() {
expect |"\0aaaa\U{0002}"| == |"?a????"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaaa\U{0002}", "?a????");
expect r0 <==> forall n :: 0 <= n < |"\0aaaa\U{0002}"| ==> "\0aaaa\U{0002}"[n] == "?a????"[n] || "?a????"[n] == '?';
}
method {:test} Test31() {
expect |"aaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaa\0\U{000C}aaaa"| == |"aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}\U{0002}aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaa\0\U{000C}aaaa", "aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}\U{0002}aaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaa\0\U{000C}aaaa"| ==> "aaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaa\0\U{000C}aaaa"[n] == "aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}\U{0002}aaaaa"[n] || "aaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}\U{0002}aaaaa"[n] == '?';
}

// REPEAT 7 - TIME: 20.7144219 s

method {:test} Test32() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa"| == |"aaaaaaaaaaaa?aaaaaaaaaaaaaaaaaaa?aaaaaaa??aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa", "aaaaaaaaaaaa?aaaaaaaaaaaaaaaaaaa?aaaaaaa??aaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa"[n] == "aaaaaaaaaaaa?aaaaaaaaaaaaaaaaaaa?aaaaaaa??aaa"[n] || "aaaaaaaaaaaa?aaaaaaaaaaaaaaaaaaa?aaaaaaa??aaa"[n] == '?';
}
method {:test} Test33() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaa\U{000E}"| == |"aaaaa\U{0008}aaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\n\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaa\U{000E}", "aaaaa\U{0008}aaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\n\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaa\U{000E}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaa\U{000E}"[n] == "aaaaa\U{0008}aaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\n\U{000C}"[n] || "aaaaa\U{0008}aaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\n\U{000C}"[n] == '?';
}

// REPEAT 8 - TIME: 22.086212 s

method {:test} Test34() {
expect |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"| == |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a", "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"| ==> "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"[n] == "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"[n] || "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"[n] == '?';
}
method {:test} Test35() {
expect |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}"| == |"aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}", "aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}"| ==> "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}"[n] == "aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a"[n] || "aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a"[n] == '?';
}

// REPEAT 9 - TIME: 23.7301933 s

method {:test} Test36() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aa\U{0001}"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa??aa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aa\U{0001}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa??aa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aa\U{0001}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aa\U{0001}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa??aa?"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa??aa?"[n] == '?';
}
method {:test} Test37() {
expect |"aaaaa\0aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{0006}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{0006}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaa\0aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{0006}aa"[n] || "aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{0006}aa"[n] == '?';
}

// REPEAT 10 - TIME: 25.5909196 s
