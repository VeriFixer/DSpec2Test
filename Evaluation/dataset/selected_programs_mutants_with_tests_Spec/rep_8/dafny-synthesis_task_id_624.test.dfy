
method {:test} Test7() {
var r0 := ToUppercase("]Ta");
expect |r0| == |"]Ta"|;
expect forall i :: 0 <= i < |"]Ta"| ==> if IsLowerCase("]Ta"[i]) then IsLowerUpperPair("]Ta"[i], r0[i]) else r0[i] == "]Ta"[i];
}

// REPEAT 8 - TIME: 9.2135986 s