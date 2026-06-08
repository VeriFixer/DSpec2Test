
method {:test} Test12() {
var r0 := ToUppercase("\\a");
expect |r0| == |"\\a"|;
expect forall i :: 0 <= i < |"\\a"| ==> if IsLowerCase("\\a"[i]) then IsLowerUpperPair("\\a"[i], r0[i]) else r0[i] == "\\a"[i];
}

// REPEAT 4 - TIME: 10.631301 s