
method {:test} Test13() {
var r0 := ToUppercase(":aa");
expect |r0| == |":aa"|;
expect forall i :: 0 <= i < |":aa"| ==> if IsLowerCase(":aa"[i]) then IsLowerUpperPair(":aa"[i], r0[i]) else r0[i] == ":aa"[i];
}

// REPEAT 5 - TIME: 11.4847392 s