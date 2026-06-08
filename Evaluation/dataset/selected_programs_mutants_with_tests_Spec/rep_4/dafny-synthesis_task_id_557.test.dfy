
method {:test} Test3() {
var r0 := ToggleCase("a\U{001A}a");
expect |r0| == |"a\U{001A}a"|;
expect forall i :: 0 <= i < |"a\U{001A}a"| ==> if IsLowerCase("a\U{001A}a"[i]) then IsLowerUpperPair("a\U{001A}a"[i], r0[i]) else if IsUpperCase("a\U{001A}a"[i]) then IsUpperLowerPair("a\U{001A}a"[i], r0[i]) else r0[i] == "a\U{001A}a"[i];
}

// REPEAT 4 - TIME: 6.6862947 s