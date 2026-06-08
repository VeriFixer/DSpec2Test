
method {:test} Test6() {
var r0 := SplitStringIntoChars("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[i];
}

// REPEAT 7 - TIME: 63.5126816 s