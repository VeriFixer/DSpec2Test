
method {:test} Test8() {
var r0 := ToUppercase("Ta");
expect |r0| == |"Ta"|;
expect forall i :: 0 <= i < |"Ta"| ==> if IsLowerCase("Ta"[i]) then IsLowerUpperPair("Ta"[i], r0[i]) else r0[i] == "Ta"[i];
}
method {:test} Test9() {
var r0 := ToUppercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test10() {
var r0 := ToUppercase("\U{0018}");
expect |r0| == |"\U{0018}"|;
expect forall i :: 0 <= i < |"\U{0018}"| ==> if IsLowerCase("\U{0018}"[i]) then IsLowerUpperPair("\U{0018}"[i], r0[i]) else r0[i] == "\U{0018}"[i];
}
method {:test} Test11() {
var r0 := ToUppercase("\U{000C}:");
expect |r0| == |"\U{000C}:"|;
expect forall i :: 0 <= i < |"\U{000C}:"| ==> if IsLowerCase("\U{000C}:"[i]) then IsLowerUpperPair("\U{000C}:"[i], r0[i]) else r0[i] == "\U{000C}:"[i];
}

// REPEAT 3 - TIME: 9.2918675 s