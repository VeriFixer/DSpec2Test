
method {:test} Test14() {
var r0 := ToLowercase("aa aaaa \U{000F}");
expect |r0| == |"aa aaaa \U{000F}"|;
expect forall i :: 0 <= i < |"aa aaaa \U{000F}"| ==> if IsUpperCase("aa aaaa \U{000F}"[i]) then IsUpperLowerPair("aa aaaa \U{000F}"[i], r0[i]) else r0[i] == "aa aaaa \U{000F}"[i];
}

// REPEAT 6 - TIME: 12.0073015 s