
method {:test} Test4() {
var r0 := ToUppercase("&");
expect |r0| == |"&"|;
expect forall i :: 0 <= i < |"&"| ==> if IsLowerCase("&"[i]) then IsLowerUpperPair("&"[i], r0[i]) else r0[i] == "&"[i];
}
method {:test} Test5() {
var r0 := ToUppercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsLowerCase("aa"[i]) then IsLowerUpperPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}
method {:test} Test6() {
var r0 := ToUppercase("aaaaa\rc");
expect |r0| == |"aaaaa\rc"|;
expect forall i :: 0 <= i < |"aaaaa\rc"| ==> if IsLowerCase("aaaaa\rc"[i]) then IsLowerUpperPair("aaaaa\rc"[i], r0[i]) else r0[i] == "aaaaa\rc"[i];
}
method {:test} Test7() {
var r0 := ToUppercase(":a");
expect |r0| == |":a"|;
expect forall i :: 0 <= i < |":a"| ==> if IsLowerCase(":a"[i]) then IsLowerUpperPair(":a"[i], r0[i]) else r0[i] == ":a"[i];
}

// REPEAT 2 - TIME: 6.9280667 s