
method {:test} Test1() {
var r0 := ToUppercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsLowerCase("aa"[i]) then IsLowerUpperPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 2 - TIME: 4.5394667 s