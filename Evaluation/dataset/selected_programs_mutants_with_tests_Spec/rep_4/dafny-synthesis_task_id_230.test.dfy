
method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("\0 ", '\0');
expect |r0| == |"\0 "|;
expect forall i :: 0 <= i < |"\0 "| ==> ("\0 "[i] == ' ' ==> r0[i] == '\0') && ("\0 "[i] != ' ' ==> r0[i] == "\0 "[i]);
}

// REPEAT 4 - TIME: 5.8908662 s