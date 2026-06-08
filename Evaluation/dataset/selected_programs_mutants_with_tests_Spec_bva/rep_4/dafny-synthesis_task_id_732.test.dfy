
method {:test} Test12() {
var r0 := ReplaceWithColon("aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa ");
expect |r0| == |"aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "| ==> (IsSpaceCommaDot("aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "[i]) ==> r0[i] == "aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "[i]);
}

// REPEAT 4 - TIME: 9.3193361 s