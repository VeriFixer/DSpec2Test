
method {:test} Test9() {
var r0 := ToLowercase("a\U{0010}aa  ");
expect |r0| == |"a\U{0010}aa  "|;
expect forall i :: 0 <= i < |"a\U{0010}aa  "| ==> if IsUpperCase("a\U{0010}aa  "[i]) then IsUpperLowerPair("a\U{0010}aa  "[i], r0[i]) else r0[i] == "a\U{0010}aa  "[i];
}

// REPEAT 10 - TIME: 13.0479961 s