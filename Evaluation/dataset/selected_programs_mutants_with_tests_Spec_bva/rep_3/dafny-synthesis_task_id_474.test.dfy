
method {:test} Test11() {
var r0 := ReplaceChars("aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", '\U{0001}', '\0');
expect |r0| == |"aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"|;
expect forall i :: 0 <= i < |"aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"| ==> ("aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] != '\U{0001}' ==> r0[i] == "aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[i]);
}

// REPEAT 3 - TIME: 8.4364092 s