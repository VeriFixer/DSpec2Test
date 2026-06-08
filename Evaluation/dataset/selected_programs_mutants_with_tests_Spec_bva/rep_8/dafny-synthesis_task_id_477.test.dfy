
method {:test} Test16() {
var r0 := ToLowercase("aaaaaaaa  -");
expect |r0| == |"aaaaaaaa  -"|;
expect forall i :: 0 <= i < |"aaaaaaaa  -"| ==> if IsUpperCase("aaaaaaaa  -"[i]) then IsUpperLowerPair("aaaaaaaa  -"[i], r0[i]) else r0[i] == "aaaaaaaa  -"[i];
}

// REPEAT 8 - TIME: 13.5459364 s