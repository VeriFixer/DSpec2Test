
method {:test} Test8() {
var r0 := ToLowercase("\U{0014}1- \U{0003}");
expect |r0| == |"\U{0014}1- \U{0003}"|;
expect forall i :: 0 <= i < |"\U{0014}1- \U{0003}"| ==> if IsUpperCase("\U{0014}1- \U{0003}"[i]) then IsUpperLowerPair("\U{0014}1- \U{0003}"[i], r0[i]) else r0[i] == "\U{0014}1- \U{0003}"[i];
}

// REPEAT 9 - TIME: 10.1525719 s