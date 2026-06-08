
method {:test} Test48() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test51() {
var r0 := ToggleCase("Ya");
expect |r0| == |"Ya"|;
expect forall i :: 0 <= i < |"Ya"| ==> if IsLowerCase("Ya"[i]) then IsLowerUpperPair("Ya"[i], r0[i]) else if IsUpperCase("Ya"[i]) then IsUpperLowerPair("Ya"[i], r0[i]) else r0[i] == "Ya"[i];
}
method {:test} Test53() {
var r0 := ToggleCase("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 9 - TIME: 34.4552137 s