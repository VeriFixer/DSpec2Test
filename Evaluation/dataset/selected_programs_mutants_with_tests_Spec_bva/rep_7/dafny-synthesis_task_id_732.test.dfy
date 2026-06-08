
method {:test} Test15() {
var r0 := ReplaceWithColon(" a aa ");
expect |r0| == |" a aa "|;
expect forall i :: 0 <= i < |" a aa "| ==> (IsSpaceCommaDot(" a aa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a aa "[i]) ==> r0[i] == " a aa "[i]);
}

// REPEAT 7 - TIME: 11.5134147 s