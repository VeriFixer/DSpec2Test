
method {:test} Test16() {
var r0 := ReplaceWithColon("  aa   a");
expect |r0| == |"  aa   a"|;
expect forall i :: 0 <= i < |"  aa   a"| ==> (IsSpaceCommaDot("  aa   a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  aa   a"[i]) ==> r0[i] == "  aa   a"[i]);
}

// REPEAT 8 - TIME: 12.2119379 s