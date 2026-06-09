
method {:test} Test9() {
var r0 := ReplaceWithColon(",  ");
expect |r0| == |",  "|;
expect forall i :: 0 <= i < |",  "| ==> (IsSpaceCommaDot(",  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",  "[i]) ==> r0[i] == ",  "[i]);
}

// REPEAT 10 - TIME: 10.5265794 s