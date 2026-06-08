
method {:test} Test8() {
var r0 := ToggleCase("\U{000F}\U{000F}aa");
expect |r0| == |"\U{000F}\U{000F}aa"|;
expect forall i :: 0 <= i < |"\U{000F}\U{000F}aa"| ==> if IsLowerCase("\U{000F}\U{000F}aa"[i]) then IsLowerUpperPair("\U{000F}\U{000F}aa"[i], r0[i]) else if IsUpperCase("\U{000F}\U{000F}aa"[i]) then IsUpperLowerPair("\U{000F}\U{000F}aa"[i], r0[i]) else r0[i] == "\U{000F}\U{000F}aa"[i];
}

// REPEAT 9 - TIME: 11.0138683 s