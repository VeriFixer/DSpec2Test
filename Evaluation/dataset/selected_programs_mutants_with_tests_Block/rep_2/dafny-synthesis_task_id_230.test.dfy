
method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("aa", '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == ' ' ==> r0[i] == '\0') && ("aa"[i] != ' ' ==> r0[i] == "aa"[i]);
}
method {:test} Test4() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaa\U{0003}", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaa\U{0003}"| ==> (" aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i]);
}
method {:test} Test5() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaa ", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaa "| ==> ("aaaaaaaaaaaaaaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaa "[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaa "[i]);
}

// REPEAT 2 - TIME: 4.4096447 s