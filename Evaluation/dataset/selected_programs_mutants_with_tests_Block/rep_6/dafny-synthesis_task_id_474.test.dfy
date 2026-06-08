
method {:test} Test15() {
var r0 := ReplaceChars("aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test16() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test17() {
var r0 := ReplaceChars("aaaa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"aaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"aaaa\U{0001}a"| ==> ("aaaa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "aaaa\U{0001}a"[i]);
}

// REPEAT 6 - TIME: 11.742331 s