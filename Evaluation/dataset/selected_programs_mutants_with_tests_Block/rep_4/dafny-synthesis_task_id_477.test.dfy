
method {:test} Test12() {
var r0 := ToLowercase("4@a");
expect |r0| == |"4@a"|;
expect forall i :: 0 <= i < |"4@a"| ==> if IsUpperCase("4@a"[i]) then IsUpperLowerPair("4@a"[i], r0[i]) else r0[i] == "4@a"[i];
}
method {:test} Test13() {
var r0 := ToLowercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test15() {
var r0 := ToLowercase(" 1aaaaaaaaaa\0aaaaaa\U{0001}");
expect |r0| == |" 1aaaaaaaaaa\0aaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |" 1aaaaaaaaaa\0aaaaaa\U{0001}"| ==> if IsUpperCase(" 1aaaaaaaaaa\0aaaaaa\U{0001}"[i]) then IsUpperLowerPair(" 1aaaaaaaaaa\0aaaaaa\U{0001}"[i], r0[i]) else r0[i] == " 1aaaaaaaaaa\0aaaaaa\U{0001}"[i];
}

// REPEAT 4 - TIME: 11.6282007 s