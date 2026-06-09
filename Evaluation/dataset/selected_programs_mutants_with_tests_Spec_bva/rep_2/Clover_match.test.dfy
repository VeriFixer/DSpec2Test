
method {:test} Test20() {
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| == |"?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}", "?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[n] == "?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?"[n] || "?aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa?"[n] == '?';
}
method {:test} Test21() {
expect |"\U{0008}\U{0004}\0"| == |"\n\U{0002}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0008}\U{0004}\0", "\n\U{0002}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"\U{0008}\U{0004}\0"| ==> "\U{0008}\U{0004}\0"[n] == "\n\U{0002}\U{0006}"[n] || "\n\U{0002}\U{0006}"[n] == '?';
}

// REPEAT 2 - TIME: 11.1987083 s