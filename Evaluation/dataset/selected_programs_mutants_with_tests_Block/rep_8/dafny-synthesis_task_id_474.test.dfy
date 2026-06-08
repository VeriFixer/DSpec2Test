
method {:test} Test21() {
var r0 := ReplaceChars("aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"|;
expect forall i :: 0 <= i < |"aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"| ==> ("aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[i]);
}
method {:test} Test22() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test23() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 8 - TIME: 14.9923215 s