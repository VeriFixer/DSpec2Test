
method {:test} Test17() {
var r0 := ReplaceChars("aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"| ==> ("aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaa\U{0001}aaaaaaaaaaaaa\U{0001}aaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}\U{0001}\U{0001}"[i]);
}

// REPEAT 9 - TIME: 12.6542551 s