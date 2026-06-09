
method {:test} Test12() {
var r0 := ToLowercase("0a");
expect |r0| == |"0a"|;
expect forall i :: 0 <= i < |"0a"| ==> if IsUpperCase("0a"[i]) then IsUpperLowerPair("0a"[i], r0[i]) else r0[i] == "0a"[i];
}

// REPEAT 4 - TIME: 9.836715 s