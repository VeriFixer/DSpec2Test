
method {:test} Test16() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a ");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "[i]);
}
method {:test} Test17() {
var r0 := ReplaceWithColon("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> (IsSpaceCommaDot("\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0"[i]) ==> r0[i] == "\0"[i]);
}
method {:test} Test18() {
var r0 := ReplaceWithColon("\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 14.8561372 s