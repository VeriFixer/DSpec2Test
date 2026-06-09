
method {:test} Test10() {
expect |"\U{0004}\0\U{0002}a"| == |"????"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0004}\0\U{0002}a", "????");
expect r0 <==> forall n :: 0 <= n < |"\U{0004}\0\U{0002}a"| ==> "\U{0004}\0\U{0002}a"[n] == "????"[n] || "????"[n] == '?';
}
method {:test} Test11() {
expect |"\U{0010}aa\naa\0a\U{0006}\U{0012}aaaaa\U{0018}"| == |"\U{001A}a\U{0004}aa\U{0014}\U{0002}a\U{000C}a\U{0008}aa\U{000E}a\U{0016}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\U{0010}aa\naa\0a\U{0006}\U{0012}aaaaa\U{0018}", "\U{001A}a\U{0004}aa\U{0014}\U{0002}a\U{000C}a\U{0008}aa\U{000E}a\U{0016}");
expect r0 <==> forall n :: 0 <= n < |"\U{0010}aa\naa\0a\U{0006}\U{0012}aaaaa\U{0018}"| ==> "\U{0010}aa\naa\0a\U{0006}\U{0012}aaaaa\U{0018}"[n] == "\U{001A}a\U{0004}aa\U{0014}\U{0002}a\U{000C}a\U{0008}aa\U{000E}a\U{0016}"[n] || "\U{001A}a\U{0004}aa\U{0014}\U{0002}a\U{000C}a\U{0008}aa\U{000E}a\U{0016}"[n] == '?';
}

// REPEAT 6 - TIME: 9.3494485 s