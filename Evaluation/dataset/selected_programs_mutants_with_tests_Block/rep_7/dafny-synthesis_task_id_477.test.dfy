
method {:test} Test24() {
var r0 := ToLowercase(" aaa\U{000F}");
expect |r0| == |" aaa\U{000F}"|;
expect forall i :: 0 <= i < |" aaa\U{000F}"| ==> if IsUpperCase(" aaa\U{000F}"[i]) then IsUpperLowerPair(" aaa\U{000F}"[i], r0[i]) else r0[i] == " aaa\U{000F}"[i];
}
method {:test} Test25() {
var r0 := ToLowercase("&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test26() {
var r0 := ToLowercase(",a\U{0007}aaa");
expect |r0| == |",a\U{0007}aaa"|;
expect forall i :: 0 <= i < |",a\U{0007}aaa"| ==> if IsUpperCase(",a\U{0007}aaa"[i]) then IsUpperLowerPair(",a\U{0007}aaa"[i], r0[i]) else r0[i] == ",a\U{0007}aaa"[i];
}
method {:test} Test27() {
var r0 := ToLowercase("-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa");
expect |r0| == |"-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"|;
expect forall i :: 0 <= i < |"-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"| ==> if IsUpperCase("-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"[i]) then IsUpperLowerPair("-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"[i], r0[i]) else r0[i] == "-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"[i];
}

// REPEAT 7 - TIME: 19.2424195 s