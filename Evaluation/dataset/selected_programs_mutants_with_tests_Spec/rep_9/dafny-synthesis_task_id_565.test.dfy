
method {:test} Test8() {
var r0 := SplitStringIntoChars("\0aaaa");
expect |r0| == |"\0aaaa"|;
expect forall i :: 0 <= i < |"\0aaaa"| ==> r0[i] == "\0aaaa"[i];
}

// REPEAT 9 - TIME: 10.2150725 s