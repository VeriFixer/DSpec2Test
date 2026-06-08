
method {:test} Test6() {
expect |"\U{0002}\0"| == |"\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0002}\0", "\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0002}\0"| ==> "\U{0002}\0"[n] == "\U{0002}\0"[n] || "\U{0002}\0"[n] == '?';
}
method {:test} Test7() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0006}\naaa\U{0004}aaa\U{0008}a\U{000C}"[n] == '?';
}
method {:test} Test8() {
expect |"\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"| == |"\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0", "\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"| ==> "\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"[n] == "\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"[n] || "\U{0004}\U{0008}aaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0"[n] == '?';
}

// REPEAT 3 - TIME: 6.4985325 s