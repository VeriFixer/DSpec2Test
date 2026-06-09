
method {:test} Test5() {
var r0 := ToLowercase("0\U{001A}1");
expect |r0| == |"0\U{001A}1"|;
expect forall i :: 0 <= i < |"0\U{001A}1"| ==> if IsUpperCase("0\U{001A}1"[i]) then IsUpperLowerPair("0\U{001A}1"[i], r0[i]) else r0[i] == "0\U{001A}1"[i];
}

// REPEAT 6 - TIME: 7.9335119 s