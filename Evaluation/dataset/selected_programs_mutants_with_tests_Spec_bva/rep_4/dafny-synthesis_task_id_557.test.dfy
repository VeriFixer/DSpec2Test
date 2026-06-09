
method {:test} Test12() {
var r0 := ToggleCase("{\U{001A}1");
expect |r0| == |"{\U{001A}1"|;
expect forall i :: 0 <= i < |"{\U{001A}1"| ==> if IsLowerCase("{\U{001A}1"[i]) then IsLowerUpperPair("{\U{001A}1"[i], r0[i]) else if IsUpperCase("{\U{001A}1"[i]) then IsUpperLowerPair("{\U{001A}1"[i], r0[i]) else r0[i] == "{\U{001A}1"[i];
}

// REPEAT 4 - TIME: 9.267968 s