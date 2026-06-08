
method {:test} Test36() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test41() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i];
}

// REPEAT 7 - TIME: 25.7268483 s