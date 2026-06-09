
method {:test} Test18() {
var r0 := ToggleCase("\U{001A}aaaa");
expect |r0| == |"\U{001A}aaaa"|;
expect forall i :: 0 <= i < |"\U{001A}aaaa"| ==> if IsLowerCase("\U{001A}aaaa"[i]) then IsLowerUpperPair("\U{001A}aaaa"[i], r0[i]) else if IsUpperCase("\U{001A}aaaa"[i]) then IsUpperLowerPair("\U{001A}aaaa"[i], r0[i]) else r0[i] == "\U{001A}aaaa"[i];
}

// REPEAT 10 - TIME: 14.0930692 s