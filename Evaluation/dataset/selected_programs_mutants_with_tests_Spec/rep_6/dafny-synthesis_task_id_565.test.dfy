
method {:test} Test5() {
var r0 := SplitStringIntoChars("\U{0002}\0a");
expect |r0| == |"\U{0002}\0a"|;
expect forall i :: 0 <= i < |"\U{0002}\0a"| ==> r0[i] == "\U{0002}\0a"[i];
}

// REPEAT 6 - TIME: 6.5634983 s