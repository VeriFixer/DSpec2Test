
method {:test} Test10() {
var r0 := ReplaceChars("aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> ("aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 7.6866143 s