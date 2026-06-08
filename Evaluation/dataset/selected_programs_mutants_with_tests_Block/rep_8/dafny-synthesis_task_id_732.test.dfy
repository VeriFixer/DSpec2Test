
method {:test} Test28() {
var r0 := ReplaceWithColon("aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}");
expect |r0| == |"aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"|;
expect forall i :: 0 <= i < |"aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"| ==> (IsSpaceCommaDot("aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"[i]) ==> r0[i] == "aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"[i]);
}
method {:test} Test29() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test31() {
var r0 := ReplaceWithColon("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 8 - TIME: 23.9398208 s