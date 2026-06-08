
method {:test} Test5() {
var r0 := ReplaceChars("\U{0001}aa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa\U{0001}a"|;
expect forall i :: 0 <= i < |"\U{0001}aa\U{0001}a"| ==> ("\U{0001}aa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa\U{0001}a"[i]);
}

// REPEAT 6 - TIME: 8.1351179 s