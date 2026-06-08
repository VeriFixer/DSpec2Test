
method {:test} Test11() {
var r0 := ToLowercase("0\U{001A}1");
expect |r0| == |"0\U{001A}1"|;
expect forall i :: 0 <= i < |"0\U{001A}1"| ==> if IsUpperCase("0\U{001A}1"[i]) then IsUpperLowerPair("0\U{001A}1"[i], r0[i]) else r0[i] == "0\U{001A}1"[i];
}

// REPEAT 3 - TIME: 9.5631841 s