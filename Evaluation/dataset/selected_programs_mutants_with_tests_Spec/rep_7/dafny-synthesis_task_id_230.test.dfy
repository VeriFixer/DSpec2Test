
method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("\U{0001} aaaaa aaaaaaa ", '\0');
expect |r0| == |"\U{0001} aaaaa aaaaaaa "|;
expect forall i :: 0 <= i < |"\U{0001} aaaaa aaaaaaa "| ==> ("\U{0001} aaaaa aaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("\U{0001} aaaaa aaaaaaa "[i] != ' ' ==> r0[i] == "\U{0001} aaaaa aaaaaaa "[i]);
}

// REPEAT 7 - TIME: 7.4287768 s