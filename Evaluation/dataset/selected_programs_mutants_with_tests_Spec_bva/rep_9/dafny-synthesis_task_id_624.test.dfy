
method {:test} Test17() {
var r0 := ToUppercase("\U{001C}(aa<aaaa\U{0017}a");
expect |r0| == |"\U{001C}(aa<aaaa\U{0017}a"|;
expect forall i :: 0 <= i < |"\U{001C}(aa<aaaa\U{0017}a"| ==> if IsLowerCase("\U{001C}(aa<aaaa\U{0017}a"[i]) then IsLowerUpperPair("\U{001C}(aa<aaaa\U{0017}a"[i], r0[i]) else r0[i] == "\U{001C}(aa<aaaa\U{0017}a"[i];
}

// REPEAT 9 - TIME: 12.7534219 s