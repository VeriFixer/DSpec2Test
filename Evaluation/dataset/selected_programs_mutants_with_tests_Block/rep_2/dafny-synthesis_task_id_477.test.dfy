
method {:test} Test4() {
var r0 := ToLowercase("&");
expect |r0| == |"&"|;
expect forall i :: 0 <= i < |"&"| ==> if IsUpperCase("&"[i]) then IsUpperLowerPair("&"[i], r0[i]) else r0[i] == "&"[i];
}
method {:test} Test5() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}
method {:test} Test6() {
var r0 := ToLowercase("aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW");
expect |r0| == |"aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"|;
expect forall i :: 0 <= i < |"aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"| ==> if IsUpperCase("aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"[i]) then IsUpperLowerPair("aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"[i], r0[i]) else r0[i] == "aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"[i];
}
method {:test} Test7() {
var r0 := ToLowercase("\U{001A}a");
expect |r0| == |"\U{001A}a"|;
expect forall i :: 0 <= i < |"\U{001A}a"| ==> if IsUpperCase("\U{001A}a"[i]) then IsUpperLowerPair("\U{001A}a"[i], r0[i]) else r0[i] == "\U{001A}a"[i];
}

// REPEAT 2 - TIME: 6.874364 s