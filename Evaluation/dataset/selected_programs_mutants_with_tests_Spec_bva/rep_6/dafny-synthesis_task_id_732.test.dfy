
method {:test} Test14() {
var r0 := ReplaceWithColon(" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa ");
expect |r0| == |" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "|;
expect forall i :: 0 <= i < |" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "| ==> (IsSpaceCommaDot(" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "[i]) ==> r0[i] == " aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "[i]);
}

// REPEAT 6 - TIME: 9.779965 s