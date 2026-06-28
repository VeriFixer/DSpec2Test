// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := s[0] < s[|s| - 1];
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

// REPEAT 1 - TIME: 12.1888433 s

method {:test} Test13() {
expect |"\U{0002}\U{0004}\0aa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}\U{0004}\0aa\U{0002}");
expect r0 <==> "\U{0002}\U{0004}\0aa\U{0002}"[0] == "\U{0002}\U{0004}\0aa\U{0002}"[|"\U{0002}\U{0004}\0aa\U{0002}"| - 1];
}
method {:test} Test14() {
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0] == "\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - 1];
}

// REPEAT 2 - TIME: 13.669768 s

method {:test} Test15() {
expect |"\0aaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaa\0");
expect r0 <==> "\0aaa\0"[0] == "\0aaa\0"[|"\0aaa\0"| - 1];
}
method {:test} Test16() {
expect |"\U{0006}\0\U{0002}a\U{0004}\U{0008}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0006}\0\U{0002}a\U{0004}\U{0008}");
expect r0 <==> "\U{0006}\0\U{0002}a\U{0004}\U{0008}"[0] == "\U{0006}\0\U{0002}a\U{0004}\U{0008}"[|"\U{0006}\0\U{0002}a\U{0004}\U{0008}"| - 1];
}

// REPEAT 3 - TIME: 14.8963486 s

method {:test} Test17() {
expect |"\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> "\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}"[0] == "\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}"[|"\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaa\U{0002}"| - 1];
}
method {:test} Test18() {
expect |"\U{0002}a\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0002}a\0");
expect r0 <==> "\U{0002}a\0"[0] == "\U{0002}a\0"[|"\U{0002}a\0"| - 1];
}

// REPEAT 4 - TIME: 16.5328736 s

method {:test} Test19() {
expect |"\0aa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aa\0");
expect r0 <==> "\0aa\0"[0] == "\0aa\0"[|"\0aa\0"| - 1];
}
method {:test} Test20() {
expect |"\U{0008}\U{0002}aaa\U{0006}\U{0004}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0008}\U{0002}aaa\U{0006}\U{0004}\0");
expect r0 <==> "\U{0008}\U{0002}aaa\U{0006}\U{0004}\0"[0] == "\U{0008}\U{0002}aaa\U{0006}\U{0004}\0"[|"\U{0008}\U{0002}aaa\U{0006}\U{0004}\0"| - 1];
}

// REPEAT 5 - TIME: 18.0803386 s

method {:test} Test21() {
expect |"\0\U{0002}\U{0004}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}\U{0004}\0");
expect r0 <==> "\0\U{0002}\U{0004}\0"[0] == "\0\U{0002}\U{0004}\0"[|"\0\U{0002}\U{0004}\0"| - 1];
}
method {:test} Test22() {
expect |"\U{000C}\U{0002}aaa\U{0006}\0\U{0004}\U{0008}\n"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{000C}\U{0002}aaa\U{0006}\0\U{0004}\U{0008}\n");
expect r0 <==> "\U{000C}\U{0002}aaa\U{0006}\0\U{0004}\U{0008}\n"[0] == "\U{000C}\U{0002}aaa\U{0006}\0\U{0004}\U{0008}\n"[|"\U{000C}\U{0002}aaa\U{0006}\0\U{0004}\U{0008}\n"| - 1];
}

// REPEAT 6 - TIME: 19.6685523 s

method {:test} Test23() {
expect |"\0\U{0002}aaaaaa\U{0004}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaaaaa\U{0004}\0");
expect r0 <==> "\0\U{0002}aaaaaa\U{0004}\0"[0] == "\0\U{0002}aaaaaa\U{0004}\0"[|"\0\U{0002}aaaaaa\U{0004}\0"| - 1];
}
method {:test} Test24() {
expect |"\U{0004}\0aaaa\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\0aaaa\U{0002}");
expect r0 <==> "\U{0004}\0aaaa\U{0002}"[0] == "\U{0004}\0aaaa\U{0002}"[|"\U{0004}\0aaaa\U{0002}"| - 1];
}

// REPEAT 7 - TIME: 21.0798544 s

method {:test} Test25() {
expect |"\0aaaa\U{0002}aaaaa\U{0004}aaaaaaa\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaa\U{0002}aaaaa\U{0004}aaaaaaa\0");
expect r0 <==> "\0aaaa\U{0002}aaaaa\U{0004}aaaaaaa\0"[0] == "\0aaaa\U{0002}aaaaa\U{0004}aaaaaaa\0"[|"\0aaaa\U{0002}aaaaa\U{0004}aaaaaaa\0"| - 1];
}
method {:test} Test26() {
expect |"\U{0004}\0aaa\na\U{000E}a\U{0010}aaaaa\U{0006}aaa\U{0008}\U{000C}aaaaa\U{0012}\U{0014}\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}\0aaa\na\U{000E}a\U{0010}aaaaa\U{0006}aaa\U{0008}\U{000C}aaaaa\U{0012}\U{0014}\U{0002}");
expect r0 <==> "\U{0004}\0aaa\na\U{000E}a\U{0010}aaaaa\U{0006}aaa\U{0008}\U{000C}aaaaa\U{0012}\U{0014}\U{0002}"[0] == "\U{0004}\0aaa\na\U{000E}a\U{0010}aaaaa\U{0006}aaa\U{0008}\U{000C}aaaaa\U{0012}\U{0014}\U{0002}"[|"\U{0004}\0aaa\na\U{000E}a\U{0010}aaaaa\U{0006}aaa\U{0008}\U{000C}aaaaa\U{0012}\U{0014}\U{0002}"| - 1];
}

// REPEAT 8 - TIME: 22.5118604 s

method {:test} Test27() {
expect |"\0\U{0002}aaa\U{0008}aaa\U{000C}\naaaaa\U{0006}aaaaaaaa\U{000E}a\U{0004}\U{0010}\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaa\U{0008}aaa\U{000C}\naaaaa\U{0006}aaaaaaaa\U{000E}a\U{0004}\U{0010}\0");
expect r0 <==> "\0\U{0002}aaa\U{0008}aaa\U{000C}\naaaaa\U{0006}aaaaaaaa\U{000E}a\U{0004}\U{0010}\0"[0] == "\0\U{0002}aaa\U{0008}aaa\U{000C}\naaaaa\U{0006}aaaaaaaa\U{000E}a\U{0004}\U{0010}\0"[|"\0\U{0002}aaa\U{0008}aaa\U{000C}\naaaaa\U{0006}aaaaaaaa\U{000E}a\U{0004}\U{0010}\0"| - 1];
}
method {:test} Test28() {
expect |"\0\U{0002}aaaaa\U{0008}a\n\U{000C}aaaaaaaa\U{0006}aaa\U{0004}aaa\U{000E}\U{0010}\U{0012}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0\U{0002}aaaaa\U{0008}a\n\U{000C}aaaaaaaa\U{0006}aaa\U{0004}aaa\U{000E}\U{0010}\U{0012}");
expect r0 <==> "\0\U{0002}aaaaa\U{0008}a\n\U{000C}aaaaaaaa\U{0006}aaa\U{0004}aaa\U{000E}\U{0010}\U{0012}"[0] == "\0\U{0002}aaaaa\U{0008}a\n\U{000C}aaaaaaaa\U{0006}aaa\U{0004}aaa\U{000E}\U{0010}\U{0012}"[|"\0\U{0002}aaaaa\U{0008}a\n\U{000C}aaaaaaaa\U{0006}aaa\U{0004}aaa\U{000E}\U{0010}\U{0012}"| - 1];
}

// REPEAT 9 - TIME: 23.9014286 s

method {:test} Test29() {
expect |"\0aaaa\U{0006}a\naa\U{000C}\U{0008}\U{0002}a\U{0004}a\0"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\0aaaa\U{0006}a\naa\U{000C}\U{0008}\U{0002}a\U{0004}a\0");
expect r0 <==> "\0aaaa\U{0006}a\naa\U{000C}\U{0008}\U{0002}a\U{0004}a\0"[0] == "\0aaaa\U{0006}a\naa\U{000C}\U{0008}\U{0002}a\U{0004}a\0"[|"\0aaaa\U{0006}a\naa\U{000C}\U{0008}\U{0002}a\U{0004}a\0"| - 1];
}
method {:test} Test30() {
expect |"\U{0014}\0aaa\U{0008}a\na\U{000E}aaaa\U{0010}\U{000C}aaa\U{0002}a\U{0006}\U{0004}\U{0012}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0014}\0aaa\U{0008}a\na\U{000E}aaaa\U{0010}\U{000C}aaa\U{0002}a\U{0006}\U{0004}\U{0012}");
expect r0 <==> "\U{0014}\0aaa\U{0008}a\na\U{000E}aaaa\U{0010}\U{000C}aaa\U{0002}a\U{0006}\U{0004}\U{0012}"[0] == "\U{0014}\0aaa\U{0008}a\na\U{000E}aaaa\U{0010}\U{000C}aaa\U{0002}a\U{0006}\U{0004}\U{0012}"[|"\U{0014}\0aaa\U{0008}a\na\U{000E}aaaa\U{0010}\U{000C}aaa\U{0002}a\U{0006}\U{0004}\U{0012}"| - 1];
}

// REPEAT 10 - TIME: 25.2624997 s
