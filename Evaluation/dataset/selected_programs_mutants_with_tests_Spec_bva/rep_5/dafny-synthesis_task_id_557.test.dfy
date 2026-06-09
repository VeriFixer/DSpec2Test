
method {:test} Test13() {
var r0 := ToggleCase(" aaaaaaaaaa aa-");
expect |r0| == |" aaaaaaaaaa aa-"|;
expect forall i :: 0 <= i < |" aaaaaaaaaa aa-"| ==> if IsLowerCase(" aaaaaaaaaa aa-"[i]) then IsLowerUpperPair(" aaaaaaaaaa aa-"[i], r0[i]) else if IsUpperCase(" aaaaaaaaaa aa-"[i]) then IsUpperLowerPair(" aaaaaaaaaa aa-"[i], r0[i]) else r0[i] == " aaaaaaaaaa aa-"[i];
}

// REPEAT 5 - TIME: 10.0274243 s