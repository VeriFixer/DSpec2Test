
method {:test} Test24() {
var r0 := ReplaceChars("aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"| ==> ("aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"[i]);
}
method {:test} Test25() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"[i]);
}
method {:test} Test26() {
var r0 := ReplaceChars("\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"|;
expect forall i :: 0 <= i < |"\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"| ==> ("\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"[i]);
}

// REPEAT 9 - TIME: 17.1150559 s