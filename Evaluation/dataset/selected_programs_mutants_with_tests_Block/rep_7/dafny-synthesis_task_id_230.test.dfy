
method {:test} Test18() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"[i]);
}
method {:test} Test19() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i]);
}
method {:test} Test20() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 7 - TIME: 12.3438842 s