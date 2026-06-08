
method {:test} Test3() {
var r0 := ToUppercase("\\:");
expect |r0| == |"\\:"|;
expect forall i :: 0 <= i < |"\\:"| ==> if IsLowerCase("\\:"[i]) then IsLowerUpperPair("\\:"[i], r0[i]) else r0[i] == "\\:"[i];
}

// REPEAT 4 - TIME: 7.02807 s