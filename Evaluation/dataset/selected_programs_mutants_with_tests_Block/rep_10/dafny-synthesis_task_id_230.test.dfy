
method {:test} Test27() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"  aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"  aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("  aaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "  aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa aa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa aa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa aa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa aa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa aa"[i]);
}

// REPEAT 10 - TIME: 16.621221 s