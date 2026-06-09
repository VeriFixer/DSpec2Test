
method {:test} Test36() {
var r0 := ReplaceWithColon("aaaa");
expect |r0| == |"aaaa"|;
expect forall i :: 0 <= i < |"aaaa"| ==> (IsSpaceCommaDot("aaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaa"[i]) ==> r0[i] == "aaaa"[i]);
}
method {:test} Test37() {
var r0 := ReplaceWithColon(":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test38() {
var r0 := ReplaceWithColon("::");
expect |r0| == |"::"|;
expect forall i :: 0 <= i < |"::"| ==> (IsSpaceCommaDot("::"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("::"[i]) ==> r0[i] == "::"[i]);
}
method {:test} Test39() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 10 - TIME: 26.6298254 s