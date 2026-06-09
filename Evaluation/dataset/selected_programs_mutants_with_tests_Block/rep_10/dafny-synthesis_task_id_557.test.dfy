
method {:test} Test54() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test55() {
var r0 := ToggleCase("\U{0010}a");
expect |r0| == |"\U{0010}a"|;
expect forall i :: 0 <= i < |"\U{0010}a"| ==> if IsLowerCase("\U{0010}a"[i]) then IsLowerUpperPair("\U{0010}a"[i], r0[i]) else if IsUpperCase("\U{0010}a"[i]) then IsUpperLowerPair("\U{0010}a"[i], r0[i]) else r0[i] == "\U{0010}a"[i];
}
method {:test} Test56() {
var r0 := ToggleCase("\U{0019}a");
expect |r0| == |"\U{0019}a"|;
expect forall i :: 0 <= i < |"\U{0019}a"| ==> if IsLowerCase("\U{0019}a"[i]) then IsLowerUpperPair("\U{0019}a"[i], r0[i]) else if IsUpperCase("\U{0019}a"[i]) then IsUpperLowerPair("\U{0019}a"[i], r0[i]) else r0[i] == "\U{0019}a"[i];
}
method {:test} Test58() {
var r0 := ToggleCase("2a");
expect |r0| == |"2a"|;
expect forall i :: 0 <= i < |"2a"| ==> if IsLowerCase("2a"[i]) then IsLowerUpperPair("2a"[i], r0[i]) else if IsUpperCase("2a"[i]) then IsUpperLowerPair("2a"[i], r0[i]) else r0[i] == "2a"[i];
}
method {:test} Test59() {
var r0 := ToggleCase("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 10 - TIME: 34.3933864 s