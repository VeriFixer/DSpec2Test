
method {:test} Test2() {
var r0 := SplitStringIntoChars("aaa");
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> r0[i] == "aaa"[i];
}

// REPEAT 3 - TIME: 4.1647725 s