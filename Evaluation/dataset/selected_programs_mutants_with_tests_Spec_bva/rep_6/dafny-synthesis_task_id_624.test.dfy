
method {:test} Test14() {
var r0 := ToUppercase("aaTaaaa<\U{001C}");
expect |r0| == |"aaTaaaa<\U{001C}"|;
expect forall i :: 0 <= i < |"aaTaaaa<\U{001C}"| ==> if IsLowerCase("aaTaaaa<\U{001C}"[i]) then IsLowerUpperPair("aaTaaaa<\U{001C}"[i], r0[i]) else r0[i] == "aaTaaaa<\U{001C}"[i];
}

// REPEAT 6 - TIME: 12.4033466 s