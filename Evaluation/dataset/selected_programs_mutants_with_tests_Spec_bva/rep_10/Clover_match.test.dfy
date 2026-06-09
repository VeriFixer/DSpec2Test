
method {:test} Test36() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aa\U{0001}"| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa??aa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aa\U{0001}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa??aa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aa\U{0001}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aa\U{0001}"[n] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa??aa?"[n] || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa??aa?"[n] == '?';
}
method {:test} Test37() {
expect |"aaaaa\0aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| == |"aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{0006}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{0006}aa");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "aaaaa\0aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[n] == "aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{0006}aa"[n] || "aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\U{0006}aa"[n] == '?';
}

// REPEAT 10 - TIME: 18.616598 s