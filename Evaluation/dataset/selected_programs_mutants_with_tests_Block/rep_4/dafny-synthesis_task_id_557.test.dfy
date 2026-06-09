
method {:test} Test18() {
var r0 := ToggleCase("gacayaaaajqa");
expect |r0| == |"gacayaaaajqa"|;
expect forall i :: 0 <= i < |"gacayaaaajqa"| ==> if IsLowerCase("gacayaaaajqa"[i]) then IsLowerUpperPair("gacayaaaajqa"[i], r0[i]) else if IsUpperCase("gacayaaaajqa"[i]) then IsUpperLowerPair("gacayaaaajqa"[i], r0[i]) else r0[i] == "gacayaaaajqa"[i];
}
method {:test} Test19() {
var r0 := ToggleCase("Kaa");
expect |r0| == |"Kaa"|;
expect forall i :: 0 <= i < |"Kaa"| ==> if IsLowerCase("Kaa"[i]) then IsLowerUpperPair("Kaa"[i], r0[i]) else if IsUpperCase("Kaa"[i]) then IsUpperLowerPair("Kaa"[i], r0[i]) else r0[i] == "Kaa"[i];
}
method {:test} Test20() {
var r0 := ToggleCase("7a");
expect |r0| == |"7a"|;
expect forall i :: 0 <= i < |"7a"| ==> if IsLowerCase("7a"[i]) then IsLowerUpperPair("7a"[i], r0[i]) else if IsUpperCase("7a"[i]) then IsUpperLowerPair("7a"[i], r0[i]) else r0[i] == "7a"[i];
}
method {:test} Test21() {
var r0 := ToggleCase(".");
expect |r0| == |"."|;
expect forall i :: 0 <= i < |"."| ==> if IsLowerCase("."[i]) then IsLowerUpperPair("."[i], r0[i]) else if IsUpperCase("."[i]) then IsUpperLowerPair("."[i], r0[i]) else r0[i] == "."[i];
}
method {:test} Test22() {
var r0 := ToggleCase("\U{0005}aa");
expect |r0| == |"\U{0005}aa"|;
expect forall i :: 0 <= i < |"\U{0005}aa"| ==> if IsLowerCase("\U{0005}aa"[i]) then IsLowerUpperPair("\U{0005}aa"[i], r0[i]) else if IsUpperCase("\U{0005}aa"[i]) then IsUpperLowerPair("\U{0005}aa"[i], r0[i]) else r0[i] == "\U{0005}aa"[i];
}
method {:test} Test23() {
var r0 := ToggleCase("bT\U{0004}\U{0006}\0");
expect |r0| == |"bT\U{0004}\U{0006}\0"|;
expect forall i :: 0 <= i < |"bT\U{0004}\U{0006}\0"| ==> if IsLowerCase("bT\U{0004}\U{0006}\0"[i]) then IsLowerUpperPair("bT\U{0004}\U{0006}\0"[i], r0[i]) else if IsUpperCase("bT\U{0004}\U{0006}\0"[i]) then IsUpperLowerPair("bT\U{0004}\U{0006}\0"[i], r0[i]) else r0[i] == "bT\U{0004}\U{0006}\0"[i];
}

// REPEAT 4 - TIME: 14.3644382 s