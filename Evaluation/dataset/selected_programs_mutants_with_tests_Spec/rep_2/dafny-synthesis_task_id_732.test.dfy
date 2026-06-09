
method {:test} Test1() {
var r0 := ReplaceWithColon("a\0");
expect |r0| == |"a\0"|;
expect forall i :: 0 <= i < |"a\0"| ==> (IsSpaceCommaDot("a\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0"[i]) ==> r0[i] == "a\0"[i]);
}

// REPEAT 2 - TIME: 3.7459485 s