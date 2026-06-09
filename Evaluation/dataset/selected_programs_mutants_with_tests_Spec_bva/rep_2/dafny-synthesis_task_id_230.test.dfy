
method {:test} Test10() {
var r0 := ReplaceBlanksWithChar(" \0", '\0');
expect |r0| == |" \0"|;
expect forall i :: 0 <= i < |" \0"| ==> (" \0"[i] == ' ' ==> r0[i] == '\0') && (" \0"[i] != ' ' ==> r0[i] == " \0"[i]);
}

// REPEAT 2 - TIME: 7.4006475 s