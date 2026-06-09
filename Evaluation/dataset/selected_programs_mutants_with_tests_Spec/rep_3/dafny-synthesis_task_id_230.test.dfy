
method {:test} Test2() {
var r0 := ReplaceBlanksWithChar("  ", '\0');
expect |r0| == |"  "|;
expect forall i :: 0 <= i < |"  "| ==> ("  "[i] == ' ' ==> r0[i] == '\0') && ("  "[i] != ' ' ==> r0[i] == "  "[i]);
}

// REPEAT 3 - TIME: 4.3063994 s