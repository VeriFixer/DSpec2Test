
method {:test} Test17() {
var r0 := ToLowercase("-aaaa aaa0 -");
expect |r0| == |"-aaaa aaa0 -"|;
expect forall i :: 0 <= i < |"-aaaa aaa0 -"| ==> if IsUpperCase("-aaaa aaa0 -"[i]) then IsUpperLowerPair("-aaaa aaa0 -"[i], r0[i]) else r0[i] == "-aaaa aaa0 -"[i];
}

// REPEAT 9 - TIME: 13.4803607 s