
method {:test} Test5() {
var r0 := SplitStringIntoChars("\0aa\U{0002}");
expect |r0| == |"\0aa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aa\U{0002}"| ==> r0[i] == "\0aa\U{0002}"[i];
}

// REPEAT 6 - TIME: 6.0565761 s