
method {:test} Test32() {
var r0 := ToUppercase("aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9");
expect |r0| == |"aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"|;
expect forall i :: 0 <= i < |"aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"| ==> if IsLowerCase("aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"[i]) then IsLowerUpperPair("aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"[i], r0[i]) else r0[i] == "aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"[i];
}
method {:test} Test33() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToUppercase("Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}");
expect |r0| == |"Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"|;
expect forall i :: 0 <= i < |"Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"| ==> if IsLowerCase("Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"[i]) then IsLowerUpperPair("Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"[i], r0[i]) else r0[i] == "Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"[i];
}

// REPEAT 9 - TIME: 23.7934206 s