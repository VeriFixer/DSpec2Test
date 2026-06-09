
method {:test} Test14() {
var r0 := ToggleCase("!aaaaaaaaaaaaaa-");
expect |r0| == |"!aaaaaaaaaaaaaa-"|;
expect forall i :: 0 <= i < |"!aaaaaaaaaaaaaa-"| ==> if IsLowerCase("!aaaaaaaaaaaaaa-"[i]) then IsLowerUpperPair("!aaaaaaaaaaaaaa-"[i], r0[i]) else if IsUpperCase("!aaaaaaaaaaaaaa-"[i]) then IsUpperLowerPair("!aaaaaaaaaaaaaa-"[i], r0[i]) else r0[i] == "!aaaaaaaaaaaaaa-"[i];
}

// REPEAT 6 - TIME: 11.0913674 s