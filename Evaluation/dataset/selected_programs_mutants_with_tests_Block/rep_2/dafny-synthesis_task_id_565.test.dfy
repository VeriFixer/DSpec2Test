
method {:test} Test1() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 2 - TIME: 3.2196149 s