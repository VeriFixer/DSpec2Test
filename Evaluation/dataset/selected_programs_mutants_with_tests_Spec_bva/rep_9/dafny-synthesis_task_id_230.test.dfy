
method {:test} Test17() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaa  a ", '\0');
expect |r0| == |"  aaaaaaaaaa  a "|;
expect forall i :: 0 <= i < |"  aaaaaaaaaa  a "| ==> ("  aaaaaaaaaa  a "[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaa  a "[i] != ' ' ==> r0[i] == "  aaaaaaaaaa  a "[i]);
}

// REPEAT 9 - TIME: 12.4927502 s