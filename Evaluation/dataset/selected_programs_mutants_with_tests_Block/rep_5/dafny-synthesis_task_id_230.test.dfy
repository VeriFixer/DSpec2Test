
method {:test} Test12() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test13() {
var r0 := ReplaceBlanksWithChar("\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa", '\0');
expect |r0| == |"\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"|;
expect forall i :: 0 <= i < |"\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"| ==> ("\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"[i] != ' ' ==> r0[i] == "\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"[i]);
}
method {:test} Test14() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa", '\0');
expect |r0| == |"aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"| ==> ("aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"[i]);
}

// REPEAT 5 - TIME: 9.1519547 s