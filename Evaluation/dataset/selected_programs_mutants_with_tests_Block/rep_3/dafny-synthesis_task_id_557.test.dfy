
method {:test} Test12() {
var r0 := ToggleCase("kaag");
expect |r0| == |"kaag"|;
expect forall i :: 0 <= i < |"kaag"| ==> if IsLowerCase("kaag"[i]) then IsLowerUpperPair("kaag"[i], r0[i]) else if IsUpperCase("kaag"[i]) then IsUpperLowerPair("kaag"[i], r0[i]) else r0[i] == "kaag"[i];
}
method {:test} Test13() {
var r0 := ToggleCase("[C\U{0015}a");
expect |r0| == |"[C\U{0015}a"|;
expect forall i :: 0 <= i < |"[C\U{0015}a"| ==> if IsLowerCase("[C\U{0015}a"[i]) then IsLowerUpperPair("[C\U{0015}a"[i], r0[i]) else if IsUpperCase("[C\U{0015}a"[i]) then IsUpperLowerPair("[C\U{0015}a"[i], r0[i]) else r0[i] == "[C\U{0015}a"[i];
}
method {:test} Test14() {
var r0 := ToggleCase("sa");
expect |r0| == |"sa"|;
expect forall i :: 0 <= i < |"sa"| ==> if IsLowerCase("sa"[i]) then IsLowerUpperPair("sa"[i], r0[i]) else if IsUpperCase("sa"[i]) then IsUpperLowerPair("sa"[i], r0[i]) else r0[i] == "sa"[i];
}
method {:test} Test15() {
var r0 := ToggleCase("-");
expect |r0| == |"-"|;
expect forall i :: 0 <= i < |"-"| ==> if IsLowerCase("-"[i]) then IsLowerUpperPair("-"[i], r0[i]) else if IsUpperCase("-"[i]) then IsUpperLowerPair("-"[i], r0[i]) else r0[i] == "-"[i];
}
method {:test} Test16() {
var r0 := ToggleCase("araa");
expect |r0| == |"araa"|;
expect forall i :: 0 <= i < |"araa"| ==> if IsLowerCase("araa"[i]) then IsLowerUpperPair("araa"[i], r0[i]) else if IsUpperCase("araa"[i]) then IsUpperLowerPair("araa"[i], r0[i]) else r0[i] == "araa"[i];
}
method {:test} Test17() {
var r0 := ToggleCase("g\U{0004}bg");
expect |r0| == |"g\U{0004}bg"|;
expect forall i :: 0 <= i < |"g\U{0004}bg"| ==> if IsLowerCase("g\U{0004}bg"[i]) then IsLowerUpperPair("g\U{0004}bg"[i], r0[i]) else if IsUpperCase("g\U{0004}bg"[i]) then IsUpperLowerPair("g\U{0004}bg"[i], r0[i]) else r0[i] == "g\U{0004}bg"[i];
}

// REPEAT 3 - TIME: 11.77369 s