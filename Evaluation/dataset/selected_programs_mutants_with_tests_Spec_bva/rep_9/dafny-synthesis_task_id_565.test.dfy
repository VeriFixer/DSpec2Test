
method {:test} Test17() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}

// REPEAT 9 - TIME: 12.204572 s