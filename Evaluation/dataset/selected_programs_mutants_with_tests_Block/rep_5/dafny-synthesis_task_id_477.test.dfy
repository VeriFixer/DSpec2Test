
method {:test} Test16() {
var r0 := ToLowercase(",a-aaaaaaa2aaaaaaaaa>");
expect |r0| == |",a-aaaaaaa2aaaaaaaaa>"|;
expect forall i :: 0 <= i < |",a-aaaaaaa2aaaaaaaaa>"| ==> if IsUpperCase(",a-aaaaaaa2aaaaaaaaa>"[i]) then IsUpperLowerPair(",a-aaaaaaa2aaaaaaaaa>"[i], r0[i]) else r0[i] == ",a-aaaaaaa2aaaaaaaaa>"[i];
}
method {:test} Test17() {
var r0 := ToLowercase("\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<");
expect |r0| == |"\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"|;
expect forall i :: 0 <= i < |"\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"| ==> if IsUpperCase("\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"[i]) then IsUpperLowerPair("\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"[i], r0[i]) else r0[i] == "\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"[i];
}
method {:test} Test18() {
var r0 := ToLowercase("<aaa");
expect |r0| == |"<aaa"|;
expect forall i :: 0 <= i < |"<aaa"| ==> if IsUpperCase("<aaa"[i]) then IsUpperLowerPair("<aaa"[i], r0[i]) else r0[i] == "<aaa"[i];
}
method {:test} Test19() {
var r0 := ToLowercase("a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}");
expect |r0| == |"a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"|;
expect forall i :: 0 <= i < |"a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"| ==> if IsUpperCase("a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"[i]) then IsUpperLowerPair("a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"[i], r0[i]) else r0[i] == "a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"[i];
}

// REPEAT 5 - TIME: 14.3367011 s