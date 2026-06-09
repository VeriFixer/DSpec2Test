
method {:test} Test12() {
var r0 := ReplaceChars("\U{0006}aa\U{0002}\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\U{0006}aa\U{0002}\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0006}aa\U{0002}\U{0004}"| ==> ("\U{0006}aa\U{0002}\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0006}aa\U{0002}\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\U{0006}aa\U{0002}\U{0004}"[i]);
}
method {:test} Test13() {
var r0 := ReplaceChars("\U{0004}\U{0006}\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0004}\U{0006}\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0004}\U{0006}\U{0002}"| ==> ("\U{0004}\U{0006}\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0004}\U{0006}\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0004}\U{0006}\U{0002}"[i]);
}
method {:test} Test14() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"| ==> ("\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"[i]);
}

// REPEAT 5 - TIME: 9.5343039 s