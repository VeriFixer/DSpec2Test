
method {:test} Test4() {
var r0 := ToUppercase("\U{000C}:");
expect |r0| == |"\U{000C}:"|;
expect forall i :: 0 <= i < |"\U{000C}:"| ==> if IsLowerCase("\U{000C}:"[i]) then IsLowerUpperPair("\U{000C}:"[i], r0[i]) else r0[i] == "\U{000C}:"[i];
}

// REPEAT 5 - TIME: 8.0562187 s