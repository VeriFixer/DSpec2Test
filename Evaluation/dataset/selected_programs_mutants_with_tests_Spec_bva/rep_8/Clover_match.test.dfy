
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

// REPEAT 8 - TIME: 19.0976911 s