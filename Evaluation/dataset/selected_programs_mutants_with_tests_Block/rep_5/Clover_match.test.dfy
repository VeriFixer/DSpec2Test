
method {:test} Test12() {
expect |"aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"| == |"aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}", "aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"| ==> "aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"[n] == "aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"[n] || "aaa\U{000C}a\naaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0006}aaaaaa\U{0004}\U{0008}"[n] == '?';
}
method {:test} Test13() {
expect |"aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa"| == |"aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa", "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa"| ==> "aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa"[n] == "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}"[n] || "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0008}"[n] == '?';
}
method {:test} Test14() {
expect |"\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{000E}a\U{0008}a"| == |"\U{0012}\0a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\na\U{000C}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{000E}a\U{0008}a", "\U{0012}\0a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\na\U{000C}aaaaaa");
expect r0 <==> forall n :: 0 <= n < |"\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{000E}a\U{0008}a"| ==> "\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{000E}a\U{0008}a"[n] == "\U{0012}\0a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\na\U{000C}aaaaaa"[n] || "\U{0012}\0a\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\na\U{000C}aaaaaa"[n] == '?';
}

// REPEAT 5 - TIME: 10.4412866 s