
method {:test} Test8() {
var r0 := ToLowercase(" a\U{000F}");
expect |r0| == |" a\U{000F}"|;
expect forall i :: 0 <= i < |" a\U{000F}"| ==> if IsUpperCase(" a\U{000F}"[i]) then IsUpperLowerPair(" a\U{000F}"[i], r0[i]) else r0[i] == " a\U{000F}"[i];
}
method {:test} Test9() {
var r0 := ToLowercase("%aaaaaa\U{0003}aaaaaa>");
expect |r0| == |"%aaaaaa\U{0003}aaaaaa>"|;
expect forall i :: 0 <= i < |"%aaaaaa\U{0003}aaaaaa>"| ==> if IsUpperCase("%aaaaaa\U{0003}aaaaaa>"[i]) then IsUpperLowerPair("%aaaaaa\U{0003}aaaaaa>"[i], r0[i]) else r0[i] == "%aaaaaa\U{0003}aaaaaa>"[i];
}
method {:test} Test10() {
var r0 := ToLowercase("\n");
expect |r0| == |"\n"|;
expect forall i :: 0 <= i < |"\n"| ==> if IsUpperCase("\n"[i]) then IsUpperLowerPair("\n"[i], r0[i]) else r0[i] == "\n"[i];
}
method {:test} Test11() {
var r0 := ToLowercase(" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0");
expect |r0| == |" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"| ==> if IsUpperCase(" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i]) then IsUpperLowerPair(" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i], r0[i]) else r0[i] == " a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i];
}

// REPEAT 3 - TIME: 8.5342768 s