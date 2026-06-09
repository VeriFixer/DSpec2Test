
method {:test} Test8() {
var r0 := ToUppercase("\U{0017}:");
expect |r0| == |"\U{0017}:"|;
expect forall i :: 0 <= i < |"\U{0017}:"| ==> if IsLowerCase("\U{0017}:"[i]) then IsLowerUpperPair("\U{0017}:"[i], r0[i]) else r0[i] == "\U{0017}:"[i];
}

// REPEAT 9 - TIME: 9.9586264 s