
method {:test} Test6() {
var r0 := ReplaceChars("aaaaa\U{0002}aaaaaa\U{0004}\U{0006}", '\U{0001}', '\0');
expect |r0| == |"aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"|;
expect forall i :: 0 <= i < |"aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"| ==> ("aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"[i] != '\U{0001}' ==> r0[i] == "aaaaa\U{0002}aaaaaa\U{0004}\U{0006}"[i]);
}

// REPEAT 7 - TIME: 8.9838862 s