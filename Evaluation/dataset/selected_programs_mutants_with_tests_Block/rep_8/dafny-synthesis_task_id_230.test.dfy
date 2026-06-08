
method {:test} Test21() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"[i]);
}
method {:test} Test22() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test23() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"| ==> ("aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"[i]);
}

// REPEAT 8 - TIME: 14.0658088 s