
method {:test} Test4() {
var r0 := ReplaceWithColon("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> (IsSpaceCommaDot("\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0"[i]) ==> r0[i] == "\0"[i]);
}
method {:test} Test7() {
var r0 := ReplaceWithColon("a\0\U{0002}");
expect |r0| == |"a\0\U{0002}"|;
expect forall i :: 0 <= i < |"a\0\U{0002}"| ==> (IsSpaceCommaDot("a\0\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0\U{0002}"[i]) ==> r0[i] == "a\0\U{0002}"[i]);
}

// REPEAT 2 - TIME: 6.4415443 s