
method {:test} Test17() {
var r0 := ReplaceWithColon("\U{0003}aaaa\0\U{0001}a\U{0002}");
expect |r0| == |"\U{0003}aaaa\0\U{0001}a\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0003}aaaa\0\U{0001}a\U{0002}"| ==> (IsSpaceCommaDot("\U{0003}aaaa\0\U{0001}a\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0003}aaaa\0\U{0001}a\U{0002}"[i]) ==> r0[i] == "\U{0003}aaaa\0\U{0001}a\U{0002}"[i]);
}

// REPEAT 9 - TIME: 12.9238727 s