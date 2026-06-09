
method {:test} Test2() {
var r0 := ToggleCase("a@");
expect |r0| == |"a@"|;
expect forall i :: 0 <= i < |"a@"| ==> if IsLowerCase("a@"[i]) then IsLowerUpperPair("a@"[i], r0[i]) else if IsUpperCase("a@"[i]) then IsUpperLowerPair("a@"[i], r0[i]) else r0[i] == "a@"[i];
}

// REPEAT 3 - TIME: 4.9869747 s