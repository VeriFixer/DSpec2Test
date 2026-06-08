
method {:test} Test20() {
var r0 := ToUppercase("T");
expect |r0| == |"T"|;
expect forall i :: 0 <= i < |"T"| ==> if IsLowerCase("T"[i]) then IsLowerUpperPair("T"[i], r0[i]) else r0[i] == "T"[i];
}
method {:test} Test21() {
var r0 := ToUppercase("Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test22() {
var r0 := ToUppercase(">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase(">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair(">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == ">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test23() {
var r0 := ToUppercase("\U{001C}_a\r\U{001B}");
expect |r0| == |"\U{001C}_a\r\U{001B}"|;
expect forall i :: 0 <= i < |"\U{001C}_a\r\U{001B}"| ==> if IsLowerCase("\U{001C}_a\r\U{001B}"[i]) then IsLowerUpperPair("\U{001C}_a\r\U{001B}"[i], r0[i]) else r0[i] == "\U{001C}_a\r\U{001B}"[i];
}

// REPEAT 6 - TIME: 16.7743405 s