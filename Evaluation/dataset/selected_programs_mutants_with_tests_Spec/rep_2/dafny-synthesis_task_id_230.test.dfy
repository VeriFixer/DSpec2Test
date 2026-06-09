
method {:test} Test1() {
var r0 := ReplaceBlanksWithChar("a ", '\0');
expect |r0| == |"a "|;
expect forall i :: 0 <= i < |"a "| ==> ("a "[i] == ' ' ==> r0[i] == '\0') && ("a "[i] != ' ' ==> r0[i] == "a "[i]);
}

// REPEAT 2 - TIME: 3.5569164 s