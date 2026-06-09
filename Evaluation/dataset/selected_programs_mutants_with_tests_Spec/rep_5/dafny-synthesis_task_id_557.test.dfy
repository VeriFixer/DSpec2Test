
method {:test} Test4() {
var r0 := ToggleCase("a\U{001A}aa");
expect |r0| == |"a\U{001A}aa"|;
expect forall i :: 0 <= i < |"a\U{001A}aa"| ==> if IsLowerCase("a\U{001A}aa"[i]) then IsLowerUpperPair("a\U{001A}aa"[i], r0[i]) else if IsUpperCase("a\U{001A}aa"[i]) then IsUpperLowerPair("a\U{001A}aa"[i], r0[i]) else r0[i] == "a\U{001A}aa"[i];
}

// REPEAT 5 - TIME: 6.7727491 s