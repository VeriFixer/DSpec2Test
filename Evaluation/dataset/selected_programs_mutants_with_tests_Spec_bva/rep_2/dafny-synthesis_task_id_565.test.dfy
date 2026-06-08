
method {:test} Test10() {
var r0 := SplitStringIntoChars("a\0a");
expect |r0| == |"a\0a"|;
expect forall i :: 0 <= i < |"a\0a"| ==> r0[i] == "a\0a"[i];
}

// REPEAT 2 - TIME: 7.462544 s