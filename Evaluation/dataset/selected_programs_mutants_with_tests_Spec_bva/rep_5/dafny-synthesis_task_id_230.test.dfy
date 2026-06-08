
method {:test} Test13() {
var r0 := ReplaceBlanksWithChar("a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa ", '\0');
expect |r0| == |"a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "| ==> ("a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "[i] != ' ' ==> r0[i] == "a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "[i]);
}

// REPEAT 5 - TIME: 10.3482767 s