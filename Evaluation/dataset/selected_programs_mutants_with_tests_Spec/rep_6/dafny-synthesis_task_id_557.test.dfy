
method {:test} Test5() {
var r0 := ToggleCase("0\U{000F}a a");
expect |r0| == |"0\U{000F}a a"|;
expect forall i :: 0 <= i < |"0\U{000F}a a"| ==> if IsLowerCase("0\U{000F}a a"[i]) then IsLowerUpperPair("0\U{000F}a a"[i], r0[i]) else if IsUpperCase("0\U{000F}a a"[i]) then IsUpperLowerPair("0\U{000F}a a"[i], r0[i]) else r0[i] == "0\U{000F}a a"[i];
}

// REPEAT 6 - TIME: 7.7705535 s