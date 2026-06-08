
method {:test} Test24() {
var r0 := ToUppercase("aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!");
expect |r0| == |"aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"|;
expect forall i :: 0 <= i < |"aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"| ==> if IsLowerCase("aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"[i]) then IsLowerUpperPair("aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"[i], r0[i]) else r0[i] == "aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"[i];
}
method {:test} Test25() {
var r0 := ToUppercase("\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test26() {
var r0 := ToUppercase("Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa");
expect |r0| == |"Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test27() {
var r0 := ToUppercase("<aaaaa\U{0004}\U{001C}");
expect |r0| == |"<aaaaa\U{0004}\U{001C}"|;
expect forall i :: 0 <= i < |"<aaaaa\U{0004}\U{001C}"| ==> if IsLowerCase("<aaaaa\U{0004}\U{001C}"[i]) then IsLowerUpperPair("<aaaaa\U{0004}\U{001C}"[i], r0[i]) else r0[i] == "<aaaaa\U{0004}\U{001C}"[i];
}

// REPEAT 7 - TIME: 19.5141245 s