
method {:test} Test14() {
var r0 := ReplaceBlanksWithChar("\0\0aaaaaaaaaa\0", '\0');
expect |r0| == |"\0\0aaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"\0\0aaaaaaaaaa\0"| ==> ("\0\0aaaaaaaaaa\0"[i] == ' ' ==> r0[i] == '\0') && ("\0\0aaaaaaaaaa\0"[i] != ' ' ==> r0[i] == "\0\0aaaaaaaaaa\0"[i]);
}

// REPEAT 6 - TIME: 11.4002335 s