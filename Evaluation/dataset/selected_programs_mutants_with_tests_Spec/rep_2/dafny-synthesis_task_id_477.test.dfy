
method {:test} Test1() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 2 - TIME: 5.1202793 s