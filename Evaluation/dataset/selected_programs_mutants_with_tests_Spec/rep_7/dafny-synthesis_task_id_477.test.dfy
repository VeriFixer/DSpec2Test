
method {:test} Test6() {
var r0 := ToLowercase(" aa0");
expect |r0| == |" aa0"|;
expect forall i :: 0 <= i < |" aa0"| ==> if IsUpperCase(" aa0"[i]) then IsUpperLowerPair(" aa0"[i], r0[i]) else r0[i] == " aa0"[i];
}

// REPEAT 7 - TIME: 10.6729664 s