
method {:test} Test1() {
var r0 := ReplaceChars("aaaaaaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaa\0"| ==> ("aaaaaaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaa\0"[i]);
}

// REPEAT 2 - TIME: 3.8485921 s