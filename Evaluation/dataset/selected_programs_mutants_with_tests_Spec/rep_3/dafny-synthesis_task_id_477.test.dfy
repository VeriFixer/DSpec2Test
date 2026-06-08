
method {:test} Test2() {
var r0 := ToLowercase("a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0");
expect |r0| == |"a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"|;
expect forall i :: 0 <= i < |"a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"| ==> if IsUpperCase("a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i]) then IsUpperLowerPair("a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i], r0[i]) else r0[i] == "a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i];
}

// REPEAT 3 - TIME: 6.283118 s