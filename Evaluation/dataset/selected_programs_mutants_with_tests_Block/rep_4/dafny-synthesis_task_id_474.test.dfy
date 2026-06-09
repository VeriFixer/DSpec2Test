
method {:test} Test9() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i]);
}
method {:test} Test10() {
var r0 := ReplaceChars("\U{0004}a\U{0002}\U{0006}", '\U{0001}', '\0');
expect |r0| == |"\U{0004}a\U{0002}\U{0006}"|;
expect forall i :: 0 <= i < |"\U{0004}a\U{0002}\U{0006}"| ==> ("\U{0004}a\U{0002}\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0004}a\U{0002}\U{0006}"[i] != '\U{0001}' ==> r0[i] == "\U{0004}a\U{0002}\U{0006}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceChars("\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"| ==> ("\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"[i]);
}

// REPEAT 4 - TIME: 8.0038669 s