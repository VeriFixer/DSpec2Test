
method {:test} Test12() {
var r0 := SplitStringIntoChars("a\0aaaaaaaaaaaa\U{0002}");
expect |r0| == |"a\0aaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaa\U{0002}"| ==> r0[i] == "a\0aaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 4 - TIME: 7.9447985 s