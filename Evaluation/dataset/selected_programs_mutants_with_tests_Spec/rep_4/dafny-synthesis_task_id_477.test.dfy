
method {:test} Test3() {
var r0 := ToLowercase("0\U{001A}");
expect |r0| == |"0\U{001A}"|;
expect forall i :: 0 <= i < |"0\U{001A}"| ==> if IsUpperCase("0\U{001A}"[i]) then IsUpperLowerPair("0\U{001A}"[i], r0[i]) else r0[i] == "0\U{001A}"[i];
}

// REPEAT 4 - TIME: 6.1217547 s