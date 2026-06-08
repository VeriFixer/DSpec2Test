
method {:test} Test18() {
var r0 := ToUppercase("Q\U{0004}\U{000C}a\U{001C}");
expect |r0| == |"Q\U{0004}\U{000C}a\U{001C}"|;
expect forall i :: 0 <= i < |"Q\U{0004}\U{000C}a\U{001C}"| ==> if IsLowerCase("Q\U{0004}\U{000C}a\U{001C}"[i]) then IsLowerUpperPair("Q\U{0004}\U{000C}a\U{001C}"[i], r0[i]) else r0[i] == "Q\U{0004}\U{000C}a\U{001C}"[i];
}

// REPEAT 10 - TIME: 15.2668996 s