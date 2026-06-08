
method {:test} Test22() {
expect |"\U{0004}aa\0aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"| == |"??a?aaa?aaaaaaaaaaaaaaaaaaaaaaaa?a?a?aa?"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}aa\0aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "??a?aaa?aaaaaaaaaaaaaaaaaaaaaaaa?a?a?aa?");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}aa\0aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"| ==> "\U{0004}aa\0aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[n] == "??a?aaa?aaaaaaaaaaaaaaaaaaaaaaaa?a?a?aa?"[n] || "??a?aaa?aaaaaaaaaaaaaaaaaaaaaaaa?a?a?aa?"[n] == '?';
}
method {:test} Test23() {
expect |"\na\U{0002}\U{0006}"| == |"\U{0008}a\U{0004}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\na\U{0002}\U{0006}", "\U{0008}a\U{0004}\0");
expect r0 <==> forall n :: 0 <= n < |"\na\U{0002}\U{0006}"| ==> "\na\U{0002}\U{0006}"[n] == "\U{0008}a\U{0004}\0"[n] || "\U{0008}a\U{0004}\0"[n] == '?';
}

// REPEAT 3 - TIME: 13.0751715 s