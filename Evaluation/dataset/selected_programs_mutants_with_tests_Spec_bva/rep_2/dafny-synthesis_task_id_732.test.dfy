
method {:test} Test10() {
var r0 := ReplaceWithColon("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> (IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 7.8487462 s