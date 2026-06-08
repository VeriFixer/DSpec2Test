
method {:test} Test15() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[n] == '?';
}
method {:test} Test16() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaa"[n] == '?';
}
method {:test} Test17() {
expect |"\0aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa"| == |"\0aa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa", "\0aa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa");
expect r0 <==> forall n :: 0 <= n < |"\0aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa"| ==> "\0aa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa"[n] == "\0aa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[n] || "\0aa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[n] == '?';
}

// REPEAT 6 - TIME: 12.6096956 s