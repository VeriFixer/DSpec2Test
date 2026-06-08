
method {:test} Test8() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 9 - TIME: 8.5856957 s