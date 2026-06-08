
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