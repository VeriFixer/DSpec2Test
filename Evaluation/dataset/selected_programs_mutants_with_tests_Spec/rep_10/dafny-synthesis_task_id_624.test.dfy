
method {:test} Test9() {
var r0 := ToUppercase("\\(aaa");
expect |r0| == |"\\(aaa"|;
expect forall i :: 0 <= i < |"\\(aaa"| ==> if IsLowerCase("\\(aaa"[i]) then IsLowerUpperPair("\\(aaa"[i], r0[i]) else r0[i] == "\\(aaa"[i];
}

// REPEAT 10 - TIME: 10.5556577 s