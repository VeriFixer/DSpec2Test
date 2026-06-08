
method {:test} Test7() {
var r0 := ToLowercase("6 a");
expect |r0| == |"6 a"|;
expect forall i :: 0 <= i < |"6 a"| ==> if IsUpperCase("6 a"[i]) then IsUpperLowerPair("6 a"[i], r0[i]) else r0[i] == "6 a"[i];
}

// REPEAT 8 - TIME: 11.4806945 s