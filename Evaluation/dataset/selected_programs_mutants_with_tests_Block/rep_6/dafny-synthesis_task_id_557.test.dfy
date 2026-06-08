
method {:test} Test30() {
var r0 := ToggleCase("gaaaaaa");
expect |r0| == |"gaaaaaa"|;
expect forall i :: 0 <= i < |"gaaaaaa"| ==> if IsLowerCase("gaaaaaa"[i]) then IsLowerUpperPair("gaaaaaa"[i], r0[i]) else if IsUpperCase("gaaaaaa"[i]) then IsUpperLowerPair("gaaaaaa"[i], r0[i]) else r0[i] == "gaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToggleCase("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test32() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test34() {
var r0 := ToggleCase("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToggleCase("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 6 - TIME: 22.053277 s