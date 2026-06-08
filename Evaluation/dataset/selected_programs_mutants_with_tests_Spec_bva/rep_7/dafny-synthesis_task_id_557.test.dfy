
method {:test} Test15() {
var r0 := ToggleCase("a\U{001A}a1");
expect |r0| == |"a\U{001A}a1"|;
expect forall i :: 0 <= i < |"a\U{001A}a1"| ==> if IsLowerCase("a\U{001A}a1"[i]) then IsLowerUpperPair("a\U{001A}a1"[i], r0[i]) else if IsUpperCase("a\U{001A}a1"[i]) then IsUpperLowerPair("a\U{001A}a1"[i], r0[i]) else r0[i] == "a\U{001A}a1"[i];
}

// REPEAT 7 - TIME: 12.7171237 s