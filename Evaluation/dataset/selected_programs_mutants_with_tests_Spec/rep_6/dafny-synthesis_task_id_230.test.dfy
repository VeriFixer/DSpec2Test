
method {:test} Test5() {
var r0 := ReplaceBlanksWithChar("a\U{0001}aaaaaaaaaaaa\U{0003}", '\0');
expect |r0| == |"a\U{0001}aaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"a\U{0001}aaaaaaaaaaaa\U{0003}"| ==> ("a\U{0001}aaaaaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}aaaaaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == "a\U{0001}aaaaaaaaaaaa\U{0003}"[i]);
}

// REPEAT 6 - TIME: 6.7280067 s