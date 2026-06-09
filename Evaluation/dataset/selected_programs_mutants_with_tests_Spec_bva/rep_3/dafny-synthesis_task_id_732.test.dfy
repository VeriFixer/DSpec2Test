
method {:test} Test11() {
var r0 := ReplaceWithColon(" a ");
expect |r0| == |" a "|;
expect forall i :: 0 <= i < |" a "| ==> (IsSpaceCommaDot(" a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a "[i]) ==> r0[i] == " a "[i]);
}

// REPEAT 3 - TIME: 7.5886568 s