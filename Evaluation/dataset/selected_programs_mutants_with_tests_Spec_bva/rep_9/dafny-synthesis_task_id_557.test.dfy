
method {:test} Test17() {
var r0 := ToggleCase("g aaaa");
expect |r0| == |"g aaaa"|;
expect forall i :: 0 <= i < |"g aaaa"| ==> if IsLowerCase("g aaaa"[i]) then IsLowerUpperPair("g aaaa"[i], r0[i]) else if IsUpperCase("g aaaa"[i]) then IsUpperLowerPair("g aaaa"[i], r0[i]) else r0[i] == "g aaaa"[i];
}

// REPEAT 9 - TIME: 14.1239262 s