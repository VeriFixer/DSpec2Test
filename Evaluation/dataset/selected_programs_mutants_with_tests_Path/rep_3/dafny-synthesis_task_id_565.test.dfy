
method {:test} Test2() {
var r0 := SplitStringIntoChars("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> r0[i] == ""[i];
}

// REPEAT 3 - TIME: 27.9267852 s