
method {:test} Test15() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"| ==> ("aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"[i]);
}
method {:test} Test16() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test17() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 6 - TIME: 10.6315417 s