
method {:test} Test16() {
var r0 := SplitStringIntoChars("\U{0002}\0\U{0004}a");
expect |r0| == |"\U{0002}\0\U{0004}a"|;
expect forall i :: 0 <= i < |"\U{0002}\0\U{0004}a"| ==> r0[i] == "\U{0002}\0\U{0004}a"[i];
}

// REPEAT 8 - TIME: 10.2937777 s