
method {:test} Test42() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i];
}
method {:test} Test43() {
var r0 := ToggleCase("\U{000F}a");
expect |r0| == |"\U{000F}a"|;
expect forall i :: 0 <= i < |"\U{000F}a"| ==> if IsLowerCase("\U{000F}a"[i]) then IsLowerUpperPair("\U{000F}a"[i], r0[i]) else if IsUpperCase("\U{000F}a"[i]) then IsUpperLowerPair("\U{000F}a"[i], r0[i]) else r0[i] == "\U{000F}a"[i];
}
method {:test} Test44() {
var r0 := ToggleCase("\U{0007}a");
expect |r0| == |"\U{0007}a"|;
expect forall i :: 0 <= i < |"\U{0007}a"| ==> if IsLowerCase("\U{0007}a"[i]) then IsLowerUpperPair("\U{0007}a"[i], r0[i]) else if IsUpperCase("\U{0007}a"[i]) then IsUpperLowerPair("\U{0007}a"[i], r0[i]) else r0[i] == "\U{0007}a"[i];
}
method {:test} Test45() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test47() {
var r0 := ToggleCase("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 8 - TIME: 29.599302 s