
method {:test} Test4() {
var r0 := SplitStringIntoChars("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> r0[i] == "aa"[i];
}

// REPEAT 5 - TIME: 53.2925278 s