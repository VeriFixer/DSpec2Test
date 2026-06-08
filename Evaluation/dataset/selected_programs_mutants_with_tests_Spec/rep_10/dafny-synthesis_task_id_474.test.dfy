
method {:test} Test9() {
var r0 := ReplaceChars("\U{0001}aaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaa"| ==> ("\U{0001}aaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaa"[i]);
}

// REPEAT 10 - TIME: 11.383922 s