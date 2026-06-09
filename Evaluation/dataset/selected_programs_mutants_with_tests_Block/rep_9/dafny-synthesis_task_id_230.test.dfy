
method {:test} Test24() {
var r0 := ReplaceBlanksWithChar("aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}", '\0');
expect |r0| == |"aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"|;
expect forall i :: 0 <= i < |"aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"| ==> ("aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"[i] == ' ' ==> r0[i] == '\0') && ("aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"[i] != ' ' ==> r0[i] == "aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"[i]);
}
method {:test} Test25() {
var r0 := ReplaceBlanksWithChar("\U{0001}\U{0005}a\U{0003}", '\0');
expect |r0| == |"\U{0001}\U{0005}a\U{0003}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0005}a\U{0003}"| ==> ("\U{0001}\U{0005}a\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}\U{0005}a\U{0003}"[i] != ' ' ==> r0[i] == "\U{0001}\U{0005}a\U{0003}"[i]);
}
method {:test} Test26() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"[i]);
}

// REPEAT 9 - TIME: 14.9055297 s