
method {:test} Test4() {
var r0 := ToLowercase(" \U{001A}");
expect |r0| == |" \U{001A}"|;
expect forall i :: 0 <= i < |" \U{001A}"| ==> if IsUpperCase(" \U{001A}"[i]) then IsUpperLowerPair(" \U{001A}"[i], r0[i]) else r0[i] == " \U{001A}"[i];
}

// REPEAT 5 - TIME: 7.0484032 s