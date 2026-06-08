
method {:test} Test9() {
var r0 := SplitStringIntoChars("\0aaa\U{0002}\U{0004}");
expect |r0| == |"\0aaa\U{0002}\U{0004}"|;
expect forall i :: 0 <= i < |"\0aaa\U{0002}\U{0004}"| ==> r0[i] == "\0aaa\U{0002}\U{0004}"[i];
}

// REPEAT 10 - TIME: 10.8566472 s