
method {:test} Test13() {
var r0 := ToLowercase("\U{001A}aa");
expect |r0| == |"\U{001A}aa"|;
expect forall i :: 0 <= i < |"\U{001A}aa"| ==> if IsUpperCase("\U{001A}aa"[i]) then IsUpperLowerPair("\U{001A}aa"[i], r0[i]) else r0[i] == "\U{001A}aa"[i];
}

// REPEAT 5 - TIME: 10.4969806 s