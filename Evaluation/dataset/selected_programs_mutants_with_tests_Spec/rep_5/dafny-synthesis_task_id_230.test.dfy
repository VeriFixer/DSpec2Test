
method {:test} Test4() {
var r0 := ReplaceBlanksWithChar("\0\U{0001}a", '\0');
expect |r0| == |"\0\U{0001}a"|;
expect forall i :: 0 <= i < |"\0\U{0001}a"| ==> ("\0\U{0001}a"[i] == ' ' ==> r0[i] == '\0') && ("\0\U{0001}a"[i] != ' ' ==> r0[i] == "\0\U{0001}a"[i]);
}

// REPEAT 5 - TIME: 6.8870497 s