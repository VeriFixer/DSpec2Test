
method {:test} Test6() {
var r0 := ToggleCase("aa@");
expect |r0| == |"aa@"|;
expect forall i :: 0 <= i < |"aa@"| ==> if IsLowerCase("aa@"[i]) then IsLowerUpperPair("aa@"[i], r0[i]) else if IsUpperCase("aa@"[i]) then IsUpperLowerPair("aa@"[i], r0[i]) else r0[i] == "aa@"[i];
}
method {:test} Test7() {
var r0 := ToggleCase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test8() {
var r0 := ToggleCase("afc");
expect |r0| == |"afc"|;
expect forall i :: 0 <= i < |"afc"| ==> if IsLowerCase("afc"[i]) then IsLowerUpperPair("afc"[i], r0[i]) else if IsUpperCase("afc"[i]) then IsUpperLowerPair("afc"[i], r0[i]) else r0[i] == "afc"[i];
}
method {:test} Test9() {
var r0 := ToggleCase("a{\U{000F}");
expect |r0| == |"a{\U{000F}"|;
expect forall i :: 0 <= i < |"a{\U{000F}"| ==> if IsLowerCase("a{\U{000F}"[i]) then IsLowerUpperPair("a{\U{000F}"[i], r0[i]) else if IsUpperCase("a{\U{000F}"[i]) then IsUpperLowerPair("a{\U{000F}"[i], r0[i]) else r0[i] == "a{\U{000F}"[i];
}
method {:test} Test10() {
var r0 := ToggleCase("k");
expect |r0| == |"k"|;
expect forall i :: 0 <= i < |"k"| ==> if IsLowerCase("k"[i]) then IsLowerUpperPair("k"[i], r0[i]) else if IsUpperCase("k"[i]) then IsUpperLowerPair("k"[i], r0[i]) else r0[i] == "k"[i];
}
method {:test} Test11() {
var r0 := ToggleCase("C{");
expect |r0| == |"C{"|;
expect forall i :: 0 <= i < |"C{"| ==> if IsLowerCase("C{"[i]) then IsLowerUpperPair("C{"[i], r0[i]) else if IsUpperCase("C{"[i]) then IsUpperLowerPair("C{"[i], r0[i]) else r0[i] == "C{"[i];
}

// REPEAT 2 - TIME: 9.178366 s