
method {:test} Test15() {
var r0 := ReplaceBlanksWithChar("\U{0003}\U{0001} a a aaaaaaaa", '\0');
expect |r0| == |"\U{0003}\U{0001} a a aaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0003}\U{0001} a a aaaaaaaa"| ==> ("\U{0003}\U{0001} a a aaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}\U{0001} a a aaaaaaaa"[i] != ' ' ==> r0[i] == "\U{0003}\U{0001} a a aaaaaaaa"[i]);
}

// REPEAT 7 - TIME: 10.8792933 s