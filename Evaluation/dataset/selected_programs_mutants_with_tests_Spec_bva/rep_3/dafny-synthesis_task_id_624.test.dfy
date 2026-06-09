
method {:test} Test11() {
var r0 := ToUppercase("\\:8");
expect |r0| == |"\\:8"|;
expect forall i :: 0 <= i < |"\\:8"| ==> if IsLowerCase("\\:8"[i]) then IsLowerUpperPair("\\:8"[i], r0[i]) else r0[i] == "\\:8"[i];
}

// REPEAT 3 - TIME: 8.5981352 s