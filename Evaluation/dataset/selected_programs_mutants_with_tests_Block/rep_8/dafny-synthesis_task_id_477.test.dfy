
method {:test} Test28() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"[i];
}
method {:test} Test29() {
var r0 := ToLowercase("-a-aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"-a-aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"-a-aaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("-a-aaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("-a-aaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "-a-aaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test30() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToLowercase("a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa");
expect |r0| == |"a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"|;
expect forall i :: 0 <= i < |"a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"| ==> if IsUpperCase("a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"[i]) then IsUpperLowerPair("a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"[i], r0[i]) else r0[i] == "a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"[i];
}

// REPEAT 8 - TIME: 19.5838973 s