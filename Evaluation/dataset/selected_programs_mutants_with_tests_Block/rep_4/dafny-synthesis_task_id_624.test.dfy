
method {:test} Test12() {
var r0 := ToUppercase("$a");
expect |r0| == |"$a"|;
expect forall i :: 0 <= i < |"$a"| ==> if IsLowerCase("$a"[i]) then IsLowerUpperPair("$a"[i], r0[i]) else r0[i] == "$a"[i];
}
method {:test} Test13() {
var r0 := ToUppercase("a\U{0017}<");
expect |r0| == |"a\U{0017}<"|;
expect forall i :: 0 <= i < |"a\U{0017}<"| ==> if IsLowerCase("a\U{0017}<"[i]) then IsLowerUpperPair("a\U{0017}<"[i], r0[i]) else r0[i] == "a\U{0017}<"[i];
}
method {:test} Test14() {
var r0 := ToUppercase("\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test15() {
var r0 := ToUppercase("(");
expect |r0| == |"("|;
expect forall i :: 0 <= i < |"("| ==> if IsLowerCase("("[i]) then IsLowerUpperPair("("[i], r0[i]) else r0[i] == "("[i];
}

// REPEAT 4 - TIME: 11.2155159 s