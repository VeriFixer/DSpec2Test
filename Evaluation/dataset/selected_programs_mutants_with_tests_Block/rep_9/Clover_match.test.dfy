
method {:test} Test24() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test25() {
expect |"aaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test26() {
expect |"aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 9 - TIME: 19.9432664 s