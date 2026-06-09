
method {:test} Test12() {
var r0 := ReplaceChars("\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> ("\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 4 - TIME: 8.8376372 s