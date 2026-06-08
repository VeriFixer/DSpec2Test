
method {:test} Test18() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaa  a  a  ", '\0');
expect |r0| == |" aaaaaaaa  a  a  "|;
expect forall i :: 0 <= i < |" aaaaaaaa  a  a  "| ==> (" aaaaaaaa  a  a  "[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaa  a  a  "[i] != ' ' ==> r0[i] == " aaaaaaaa  a  a  "[i]);
}

// REPEAT 10 - TIME: 15.0470614 s