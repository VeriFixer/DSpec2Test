
method {:test} Test2() {
var r0 := ReplaceChars("aa\U{0002}", '\U{0001}', '\0');
expect |r0| == |"aa\U{0002}"|;
expect forall i :: 0 <= i < |"aa\U{0002}"| ==> ("aa\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa\U{0002}"[i] != '\U{0001}' ==> r0[i] == "aa\U{0002}"[i]);
}

// REPEAT 3 - TIME: 5.0233029 s