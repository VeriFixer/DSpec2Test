
method {:test} Test15() {
var r0 := ToUppercase("\U{001C}(aaaa\\aa\U{000C}");
expect |r0| == |"\U{001C}(aaaa\\aa\U{000C}"|;
expect forall i :: 0 <= i < |"\U{001C}(aaaa\\aa\U{000C}"| ==> if IsLowerCase("\U{001C}(aaaa\\aa\U{000C}"[i]) then IsLowerUpperPair("\U{001C}(aaaa\\aa\U{000C}"[i], r0[i]) else r0[i] == "\U{001C}(aaaa\\aa\U{000C}"[i];
}

// REPEAT 7 - TIME: 11.5410982 s