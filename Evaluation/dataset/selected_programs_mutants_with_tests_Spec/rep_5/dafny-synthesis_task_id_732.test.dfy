
method {:test} Test4() {
var r0 := ReplaceWithColon(" a");
expect |r0| == |" a"|;
expect forall i :: 0 <= i < |" a"| ==> (IsSpaceCommaDot(" a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a"[i]) ==> r0[i] == " a"[i]);
}

// REPEAT 5 - TIME: 6.4775587 s