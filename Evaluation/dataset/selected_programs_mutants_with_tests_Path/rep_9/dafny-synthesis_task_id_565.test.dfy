
method {:test} Test8() {
var r0 := SplitStringIntoChars("\0aaaaaaaaaaaaa\U{0002}");
expect |r0| == |"\0aaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaa\U{0002}"| ==> r0[i] == "\0aaaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 9 - TIME: 103.350664 s