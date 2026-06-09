
method {:test} Test16() {
var r0 := ToggleCase("\U{000F}\U{001A}aa0aaaaaaaaaa ");
expect |r0| == |"\U{000F}\U{001A}aa0aaaaaaaaaa "|;
expect forall i :: 0 <= i < |"\U{000F}\U{001A}aa0aaaaaaaaaa "| ==> if IsLowerCase("\U{000F}\U{001A}aa0aaaaaaaaaa "[i]) then IsLowerUpperPair("\U{000F}\U{001A}aa0aaaaaaaaaa "[i], r0[i]) else if IsUpperCase("\U{000F}\U{001A}aa0aaaaaaaaaa "[i]) then IsUpperLowerPair("\U{000F}\U{001A}aa0aaaaaaaaaa "[i], r0[i]) else r0[i] == "\U{000F}\U{001A}aa0aaaaaaaaaa "[i];
}

// REPEAT 8 - TIME: 12.5762035 s