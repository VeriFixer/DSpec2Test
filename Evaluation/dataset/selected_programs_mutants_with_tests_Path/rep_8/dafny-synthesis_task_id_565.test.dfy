
method {:test} Test7() {
var r0 := SplitStringIntoChars("\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}");
expect |r0| == |"\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}"|;
expect forall i :: 0 <= i < |"\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}"| ==> r0[i] == "\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}"[i];
}

// REPEAT 8 - TIME: 73.07867 s