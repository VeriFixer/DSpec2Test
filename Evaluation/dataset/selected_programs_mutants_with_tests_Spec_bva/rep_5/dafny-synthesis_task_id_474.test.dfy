
method {:test} Test13() {
var r0 := ReplaceChars("\U{0001}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aa"| ==> ("\U{0001}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa"[i]);
}

// REPEAT 5 - TIME: 10.1470951 s