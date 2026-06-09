
method {:test} Test14() {
var r0 := ReplaceChars("\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 6 - TIME: 10.34047 s