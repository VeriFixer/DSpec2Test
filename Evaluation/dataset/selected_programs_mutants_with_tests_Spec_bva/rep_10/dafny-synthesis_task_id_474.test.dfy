
method {:test} Test18() {
var r0 := ReplaceChars("aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"| ==> ("aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa\U{0001}\U{0001}"[i]);
}

// REPEAT 10 - TIME: 13.3014225 s