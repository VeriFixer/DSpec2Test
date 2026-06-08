
method {:test} Test7() {
var r0 := ToggleCase("2\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{000F}");
expect |r0| == |"2\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{000F}"|;
expect forall i :: 0 <= i < |"2\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{000F}"| ==> if IsLowerCase("2\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{000F}"[i]) then IsLowerUpperPair("2\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{000F}"[i], r0[i]) else if IsUpperCase("2\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{000F}"[i]) then IsUpperLowerPair("2\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{000F}"[i], r0[i]) else r0[i] == "2\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{000F}"[i];
}

// REPEAT 8 - TIME: 10.1566473 s