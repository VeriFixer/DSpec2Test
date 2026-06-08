
method {:test} Test16() {
var r0 := ReplaceBlanksWithChar(" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a ", '\0');
expect |r0| == |" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "|;
expect forall i :: 0 <= i < |" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "| ==> (" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i] == ' ' ==> r0[i] == '\0') && (" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i] != ' ' ==> r0[i] == " a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i]);
}

// REPEAT 8 - TIME: 13.3542573 s