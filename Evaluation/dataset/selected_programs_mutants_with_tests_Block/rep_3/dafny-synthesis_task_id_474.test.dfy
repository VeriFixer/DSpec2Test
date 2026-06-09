
method {:test} Test6() {
var r0 := ReplaceChars("", '\U{0001}', '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == '\U{0001}' ==> r0[i] == '\0') && (""[i] != '\U{0001}' ==> r0[i] == ""[i]);
}
method {:test} Test7() {
var r0 := ReplaceChars("\U{0002}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aa"|;
expect forall i :: 0 <= i < |"\U{0002}aa"| ==> ("\U{0002}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aa"[i]);
}
method {:test} Test8() {
var r0 := ReplaceChars("\U{0001}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aa"| ==> ("\U{0001}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa"[i]);
}

// REPEAT 3 - TIME: 6.3899547 s