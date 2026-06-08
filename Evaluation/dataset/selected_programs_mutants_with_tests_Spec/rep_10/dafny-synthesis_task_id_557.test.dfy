
method {:test} Test9() {
var r0 := ToggleCase("-\U{0010}a \U{000F}2");
expect |r0| == |"-\U{0010}a \U{000F}2"|;
expect forall i :: 0 <= i < |"-\U{0010}a \U{000F}2"| ==> if IsLowerCase("-\U{0010}a \U{000F}2"[i]) then IsLowerUpperPair("-\U{0010}a \U{000F}2"[i], r0[i]) else if IsUpperCase("-\U{0010}a \U{000F}2"[i]) then IsUpperLowerPair("-\U{0010}a \U{000F}2"[i], r0[i]) else r0[i] == "-\U{0010}a \U{000F}2"[i];
}

// REPEAT 10 - TIME: 11.9117369 s