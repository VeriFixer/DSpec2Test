
method {:test} Test13() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}

// REPEAT 5 - TIME: 9.7316491 s