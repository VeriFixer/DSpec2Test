
method {:test} Test18() {
var r0 := ReplaceChars("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"| ==> ("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"[i]);
}
method {:test} Test19() {
var r0 := ReplaceChars("aa\U{0002}aaaa", '\U{0001}', '\0');
expect |r0| == |"aa\U{0002}aaaa"|;
expect forall i :: 0 <= i < |"aa\U{0002}aaaa"| ==> ("aa\U{0002}aaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa\U{0002}aaaa"[i] != '\U{0001}' ==> r0[i] == "aa\U{0002}aaaa"[i]);
}
method {:test} Test20() {
var r0 := ReplaceChars("a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}", '\U{0001}', '\0');
expect |r0| == |"a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"|;
expect forall i :: 0 <= i < |"a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"| ==> ("a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"[i] != '\U{0001}' ==> r0[i] == "a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"[i]);
}

// REPEAT 7 - TIME: 12.5635605 s