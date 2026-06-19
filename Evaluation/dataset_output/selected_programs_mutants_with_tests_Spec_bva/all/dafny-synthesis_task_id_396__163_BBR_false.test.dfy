// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := false;
}


method {:test} Test0() {
expect |"\0aaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\0");
expect r0 <==> "\0aaaaaaa\0"[0] == "\0aaaaaaa\0"[|"\0aaaaaaa\0"| - 1];
}
method {:test} Test1() {
expect |"\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0");
expect r0 <==> "\0"[0] == "\0"[|"\0"| - 1];
}
method {:test} Test2() {
expect |"\0\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\0");
expect r0 <==> "\0\0"[0] == "\0\0"[|"\0\0"| - 1];
}
method {:test} Test7() {
expect |"\0aaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaa\U{0002}"[0] == "\0aaaaaaa\U{0002}"[|"\0aaaaaaa\U{0002}"| - 1];
}
method {:test} Test8() {
expect |"\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}");
expect r0 <==> "\0\U{0002}"[0] == "\0\U{0002}"[|"\0\U{0002}"| - 1];
}

// REPEAT 1 - TIME: 9.2201472 s

method {:test} Test13() {
expect |"\U{0002}\U{0004}aaaaaaaaaaaaaaa\U{0006}\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\U{0004}aaaaaaaaaaaaaaa\U{0006}\0\U{0002}");
expect r0 <==> "\U{0002}\U{0004}aaaaaaaaaaaaaaa\U{0006}\0\U{0002}"[0] == "\U{0002}\U{0004}aaaaaaaaaaaaaaa\U{0006}\0\U{0002}"[|"\U{0002}\U{0004}aaaaaaaaaaaaaaa\U{0006}\0\U{0002}"| - 1];
}
method {:test} Test14() {
expect |"\0\U{0004}aaaaaaaa\U{0006}aaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0004}aaaaaaaa\U{0006}aaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\0\U{0004}aaaaaaaa\U{0006}aaaaaaaaaaaaaaaa\U{0002}"[0] == "\0\U{0004}aaaaaaaa\U{0006}aaaaaaaaaaaaaaaa\U{0002}"[|"\0\U{0004}aaaaaaaa\U{0006}aaaaaaaaaaaaaaaa\U{0002}"| - 1];
}

// REPEAT 2 - TIME: 10.322318 s

method {:test} Test15() {
expect |"\0aaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaa\0");
expect r0 <==> "\0aaaaaaaaaa\0"[0] == "\0aaaaaaaaaa\0"[|"\0aaaaaaaaaa\0"| - 1];
}
method {:test} Test16() {
expect |"\U{0006}\0aaaaaa\U{0002}\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0006}\0aaaaaa\U{0002}\U{0004}");
expect r0 <==> "\U{0006}\0aaaaaa\U{0002}\U{0004}"[0] == "\U{0006}\0aaaaaa\U{0002}\U{0004}"[|"\U{0006}\0aaaaaa\U{0002}\U{0004}"| - 1];
}

// REPEAT 3 - TIME: 11.4718458 s

method {:test} Test17() {
expect |"\U{0008}\0aaaaa\U{0002}a\U{0006}aa\U{0004}aaaaaaaaaaaaaaa\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0008}\0aaaaa\U{0002}a\U{0006}aa\U{0004}aaaaaaaaaaaaaaa\U{0008}");
expect r0 <==> "\U{0008}\0aaaaa\U{0002}a\U{0006}aa\U{0004}aaaaaaaaaaaaaaa\U{0008}"[0] == "\U{0008}\0aaaaa\U{0002}a\U{0006}aa\U{0004}aaaaaaaaaaaaaaa\U{0008}"[|"\U{0008}\0aaaaa\U{0002}a\U{0006}aa\U{0004}aaaaaaaaaaaaaaa\U{0008}"| - 1];
}
method {:test} Test18() {
expect |"\n\0aaaaa\U{0002}a\U{0006}\U{0004}aaaaaaaaaaaaaaaaa\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\n\0aaaaa\U{0002}a\U{0006}\U{0004}aaaaaaaaaaaaaaaaa\U{0008}");
expect r0 <==> "\n\0aaaaa\U{0002}a\U{0006}\U{0004}aaaaaaaaaaaaaaaaa\U{0008}"[0] == "\n\0aaaaa\U{0002}a\U{0006}\U{0004}aaaaaaaaaaaaaaaaa\U{0008}"[|"\n\0aaaaa\U{0002}a\U{0006}\U{0004}aaaaaaaaaaaaaaaaa\U{0008}"| - 1];
}

// REPEAT 4 - TIME: 12.6002865 s

method {:test} Test19() {
expect |"\U{0002}\0aaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\0aaa\U{0002}");
expect r0 <==> "\U{0002}\0aaa\U{0002}"[0] == "\U{0002}\0aaa\U{0002}"[|"\U{0002}\0aaa\U{0002}"| - 1];
}
method {:test} Test20() {
expect |"\U{0004}\U{0002}aaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\U{0002}aaa\0");
expect r0 <==> "\U{0004}\U{0002}aaa\0"[0] == "\U{0004}\U{0002}aaa\0"[|"\U{0004}\U{0002}aaa\0"| - 1];
}

// REPEAT 5 - TIME: 13.8281047 s

method {:test} Test21() {
expect |"\0aaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaa\0");
expect r0 <==> "\0aaa\0"[0] == "\0aaa\0"[|"\0aaa\0"| - 1];
}
method {:test} Test22() {
expect |"\0aaaa\U{0002}\U{0006}\U{0004}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaa\U{0002}\U{0006}\U{0004}");
expect r0 <==> "\0aaaa\U{0002}\U{0006}\U{0004}"[0] == "\0aaaa\U{0002}\U{0006}\U{0004}"[|"\0aaaa\U{0002}\U{0006}\U{0004}"| - 1];
}

// REPEAT 6 - TIME: 15.0750109 s

method {:test} Test23() {
expect |"\0\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}a\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}a\0");
expect r0 <==> "\0\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}a\0"[0] == "\0\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}a\0"[|"\0\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}a\0"| - 1];
}
method {:test} Test24() {
expect |"\0\U{0002}aaa\U{0008}aaaaaaaaaa\U{0006}aa\n\U{0010}\U{0004}aaa\U{000C}aa\U{000E}\U{0012}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaa\U{0008}aaaaaaaaaa\U{0006}aa\n\U{0010}\U{0004}aaa\U{000C}aa\U{000E}\U{0012}");
expect r0 <==> "\0\U{0002}aaa\U{0008}aaaaaaaaaa\U{0006}aa\n\U{0010}\U{0004}aaa\U{000C}aa\U{000E}\U{0012}"[0] == "\0\U{0002}aaa\U{0008}aaaaaaaaaa\U{0006}aa\n\U{0010}\U{0004}aaa\U{000C}aa\U{000E}\U{0012}"[|"\0\U{0002}aaa\U{0008}aaaaaaaaaa\U{0006}aa\n\U{0010}\U{0004}aaa\U{000C}aa\U{000E}\U{0012}"| - 1];
}

// REPEAT 7 - TIME: 16.1306283 s

method {:test} Test25() {
expect |"\0\U{0002}aaa\U{0004}aaa\U{000C}aaa\U{0012}aaaaa\U{0010}\U{0014}\U{0008}a\U{000E}\naaa\U{0006}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaa\U{0004}aaa\U{000C}aaa\U{0012}aaaaa\U{0010}\U{0014}\U{0008}a\U{000E}\naaa\U{0006}\0");
expect r0 <==> "\0\U{0002}aaa\U{0004}aaa\U{000C}aaa\U{0012}aaaaa\U{0010}\U{0014}\U{0008}a\U{000E}\naaa\U{0006}\0"[0] == "\0\U{0002}aaa\U{0004}aaa\U{000C}aaa\U{0012}aaaaa\U{0010}\U{0014}\U{0008}a\U{000E}\naaa\U{0006}\0"[|"\0\U{0002}aaa\U{0004}aaa\U{000C}aaa\U{0012}aaaaa\U{0010}\U{0014}\U{0008}a\U{000E}\naaa\U{0006}\0"| - 1];
}
method {:test} Test26() {
expect |"\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}");
expect r0 <==> "\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"[0] == "\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"[|"\U{0008}\0aaa\U{0002}aaa\U{0004}\U{0006}"| - 1];
}

// REPEAT 8 - TIME: 17.3571233 s

method {:test} Test27() {
expect |"\0\U{0002}aaa\U{0004}aaa\naaa\U{0010}aaaaaaa\U{0006}aa\U{0008}\U{000C}a\U{0012}\U{000E}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaa\U{0004}aaa\naaa\U{0010}aaaaaaa\U{0006}aa\U{0008}\U{000C}a\U{0012}\U{000E}\0");
expect r0 <==> "\0\U{0002}aaa\U{0004}aaa\naaa\U{0010}aaaaaaa\U{0006}aa\U{0008}\U{000C}a\U{0012}\U{000E}\0"[0] == "\0\U{0002}aaa\U{0004}aaa\naaa\U{0010}aaaaaaa\U{0006}aa\U{0008}\U{000C}a\U{0012}\U{000E}\0"[|"\0\U{0002}aaa\U{0004}aaa\naaa\U{0010}aaaaaaa\U{0006}aa\U{0008}\U{000C}a\U{0012}\U{000E}\0"| - 1];
}
method {:test} Test28() {
expect |"\n\0aaa\U{0004}a\U{0002}\U{0006}\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\n\0aaa\U{0004}a\U{0002}\U{0006}\U{0008}");
expect r0 <==> "\n\0aaa\U{0004}a\U{0002}\U{0006}\U{0008}"[0] == "\n\0aaa\U{0004}a\U{0002}\U{0006}\U{0008}"[|"\n\0aaa\U{0004}a\U{0002}\U{0006}\U{0008}"| - 1];
}

// REPEAT 9 - TIME: 18.517862 s

method {:test} Test29() {
expect |"\0\U{0002}aaaaaaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaaaaaaaaaa\0");
expect r0 <==> "\0\U{0002}aaaaaaaaaaa\0"[0] == "\0\U{0002}aaaaaaaaaaa\0"[|"\0\U{0002}aaaaaaaaaaa\0"| - 1];
}
method {:test} Test30() {
expect |"\U{000E}aaaa\U{0004}aaaaa\U{0008}a\U{0006}a\na\U{0002}aaa\U{000C}aaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{000E}aaaa\U{0004}aaaaa\U{0008}a\U{0006}a\na\U{0002}aaa\U{000C}aaaaa\0");
expect r0 <==> "\U{000E}aaaa\U{0004}aaaaa\U{0008}a\U{0006}a\na\U{0002}aaa\U{000C}aaaaa\0"[0] == "\U{000E}aaaa\U{0004}aaaaa\U{0008}a\U{0006}a\na\U{0002}aaa\U{000C}aaaaa\0"[|"\U{000E}aaaa\U{0004}aaaaa\U{0008}a\U{0006}a\na\U{0002}aaa\U{000C}aaaaa\0"| - 1];
}

// REPEAT 10 - TIME: 19.9975115 s
