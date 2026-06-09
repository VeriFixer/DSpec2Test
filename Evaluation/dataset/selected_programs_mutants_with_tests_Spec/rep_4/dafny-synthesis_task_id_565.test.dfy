
method {:test} Test3() {
var r0 := SplitStringIntoChars("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[i];
}

// REPEAT 4 - TIME: 5.0387787 s