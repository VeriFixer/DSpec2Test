
method {:test} Test16() {
var r0 := ToUppercase("(aa\\");
expect |r0| == |"(aa\\"|;
expect forall i :: 0 <= i < |"(aa\\"| ==> if IsLowerCase("(aa\\"[i]) then IsLowerUpperPair("(aa\\"[i], r0[i]) else r0[i] == "(aa\\"[i];
}
method {:test} Test17() {
var r0 := ToUppercase("\U{0018}aW");
expect |r0| == |"\U{0018}aW"|;
expect forall i :: 0 <= i < |"\U{0018}aW"| ==> if IsLowerCase("\U{0018}aW"[i]) then IsLowerUpperPair("\U{0018}aW"[i], r0[i]) else r0[i] == "\U{0018}aW"[i];
}
method {:test} Test18() {
var r0 := ToUppercase("\U{0015}aaa");
expect |r0| == |"\U{0015}aaa"|;
expect forall i :: 0 <= i < |"\U{0015}aaa"| ==> if IsLowerCase("\U{0015}aaa"[i]) then IsLowerUpperPair("\U{0015}aaa"[i], r0[i]) else r0[i] == "\U{0015}aaa"[i];
}
method {:test} Test19() {
var r0 := ToUppercase("\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| == |"\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> if IsLowerCase("\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i]) then IsLowerUpperPair("\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i], r0[i]) else r0[i] == "\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i];
}

// REPEAT 5 - TIME: 14.3787393 s