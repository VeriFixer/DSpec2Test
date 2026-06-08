
method {:test} Test18() {
var r0 := SplitStringIntoChars("\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| == |"\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> r0[i] == "\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i];
}

// REPEAT 10 - TIME: 12.8630241 s