
method {:test} Test32() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test33() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test34() {
var r0 := ReplaceWithColon("a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test35() {
var r0 := ReplaceWithColon("a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a");
expect |r0| == |"a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"|;
expect forall i :: 0 <= i < |"a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"| ==> (IsSpaceCommaDot("a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"[i]) ==> r0[i] == "a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"[i]);
}

// REPEAT 9 - TIME: 23.4799405 s