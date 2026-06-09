
method {:test} Test13() {
var r0 := ReplaceWithColon("aaaa ");
expect |r0| == |"aaaa "|;
expect forall i :: 0 <= i < |"aaaa "| ==> (IsSpaceCommaDot("aaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaa "[i]) ==> r0[i] == "aaaa "[i]);
}

// REPEAT 5 - TIME: 8.9764454 s