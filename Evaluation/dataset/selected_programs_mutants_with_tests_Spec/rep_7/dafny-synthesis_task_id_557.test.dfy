
method {:test} Test6() {
var r0 := ToggleCase("`{");
expect |r0| == |"`{"|;
expect forall i :: 0 <= i < |"`{"| ==> if IsLowerCase("`{"[i]) then IsLowerUpperPair("`{"[i], r0[i]) else if IsUpperCase("`{"[i]) then IsUpperLowerPair("`{"[i], r0[i]) else r0[i] == "`{"[i];
}

// REPEAT 7 - TIME: 8.5081745 s