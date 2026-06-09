
method {:test} Test6() {
var r0 := ReplaceWithColon(",  a  a");
expect |r0| == |",  a  a"|;
expect forall i :: 0 <= i < |",  a  a"| ==> (IsSpaceCommaDot(",  a  a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",  a  a"[i]) ==> r0[i] == ",  a  a"[i]);
}

// REPEAT 7 - TIME: 8.252128 s