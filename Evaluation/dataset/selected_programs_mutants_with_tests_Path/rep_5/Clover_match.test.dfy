
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

// REPEAT 5 - TIME: 145.9683915 s