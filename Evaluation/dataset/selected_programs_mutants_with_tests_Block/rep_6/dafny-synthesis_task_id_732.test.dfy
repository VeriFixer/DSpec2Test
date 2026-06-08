
method {:test} Test20() {
var r0 := ReplaceWithColon(" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  ");
expect |r0| == |" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "|;
expect forall i :: 0 <= i < |" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "| ==> (IsSpaceCommaDot(" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "[i]) ==> r0[i] == " aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "[i]);
}
method {:test} Test21() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test23() {
var r0 := ReplaceWithColon("\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a");
expect |r0| == |"\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"|;
expect forall i :: 0 <= i < |"\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"| ==> (IsSpaceCommaDot("\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"[i]) ==> r0[i] == "\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"[i]);
}

// REPEAT 6 - TIME: 17.8486768 s