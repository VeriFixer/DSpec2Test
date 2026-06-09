
method {:test} Test28() {
var r0 := ToUppercase("Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ");
expect |r0| == |"Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"|;
expect forall i :: 0 <= i < |"Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"| ==> if IsLowerCase("Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"[i]) then IsLowerUpperPair("Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"[i], r0[i]) else r0[i] == "Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"[i];
}
method {:test} Test29() {
var r0 := ToUppercase("Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test30() {
var r0 := ToUppercase("\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToUppercase("\U{0004}a\U{0001}\U{0003}a\U{0005}");
expect |r0| == |"\U{0004}a\U{0001}\U{0003}a\U{0005}"|;
expect forall i :: 0 <= i < |"\U{0004}a\U{0001}\U{0003}a\U{0005}"| ==> if IsLowerCase("\U{0004}a\U{0001}\U{0003}a\U{0005}"[i]) then IsLowerUpperPair("\U{0004}a\U{0001}\U{0003}a\U{0005}"[i], r0[i]) else r0[i] == "\U{0004}a\U{0001}\U{0003}a\U{0005}"[i];
}

// REPEAT 8 - TIME: 20.5409792 s