
method {:test} Test27() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}
method {:test} Test28() {
expect |"aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] || "aaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == '?';
}

// REPEAT 10 - TIME: 235.6115994 s