
method {:test} Test3() {
var r0 := ReplaceChars("\U{0002}a", '\U{0001}', '\0');
expect |r0| == |"\U{0002}a"|;
expect forall i :: 0 <= i < |"\U{0002}a"| ==> ("\U{0002}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}a"[i] != '\U{0001}' ==> r0[i] == "\U{0002}a"[i]);
}
method {:test} Test4() {
var r0 := ReplaceChars("\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> ("\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i]);
}
method {:test} Test5() {
var r0 := ReplaceChars("\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> ("\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 4.7817822 s