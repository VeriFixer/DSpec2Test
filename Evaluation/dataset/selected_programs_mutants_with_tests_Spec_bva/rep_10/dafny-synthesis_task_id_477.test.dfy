
method {:test} Test18() {
var r0 := ToLowercase("\U{001A}\U{001B}aa");
expect |r0| == |"\U{001A}\U{001B}aa"|;
expect forall i :: 0 <= i < |"\U{001A}\U{001B}aa"| ==> if IsUpperCase("\U{001A}\U{001B}aa"[i]) then IsUpperLowerPair("\U{001A}\U{001B}aa"[i], r0[i]) else r0[i] == "\U{001A}\U{001B}aa"[i];
}

// REPEAT 10 - TIME: 14.0676057 s