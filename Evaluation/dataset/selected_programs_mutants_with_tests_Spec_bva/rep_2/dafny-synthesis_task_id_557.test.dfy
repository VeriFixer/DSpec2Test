
method {:test} Test10() {
var r0 := ToggleCase("d&");
expect |r0| == |"d&"|;
expect forall i :: 0 <= i < |"d&"| ==> if IsLowerCase("d&"[i]) then IsLowerUpperPair("d&"[i], r0[i]) else if IsUpperCase("d&"[i]) then IsUpperLowerPair("d&"[i], r0[i]) else r0[i] == "d&"[i];
}

// REPEAT 2 - TIME: 7.6009834 s