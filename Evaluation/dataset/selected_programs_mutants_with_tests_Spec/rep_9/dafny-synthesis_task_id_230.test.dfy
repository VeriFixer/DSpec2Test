
method {:test} Test8() {
var r0 := ReplaceBlanksWithChar("\0a\0", '\0');
expect |r0| == |"\0a\0"|;
expect forall i :: 0 <= i < |"\0a\0"| ==> ("\0a\0"[i] == ' ' ==> r0[i] == '\0') && ("\0a\0"[i] != ' ' ==> r0[i] == "\0a\0"[i]);
}

// REPEAT 9 - TIME: 8.945466 s