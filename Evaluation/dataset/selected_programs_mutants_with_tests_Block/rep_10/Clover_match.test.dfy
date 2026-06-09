
method {:test} Test27() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test28() {
expect |"aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test29() {
expect |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 10 - TIME: 20.935086 s