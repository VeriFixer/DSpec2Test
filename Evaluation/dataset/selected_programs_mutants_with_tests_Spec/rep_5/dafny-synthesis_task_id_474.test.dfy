
method {:test} Test4() {
var r0 := ReplaceChars("\0aaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\0aaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaa"| ==> ("\0aaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\0aaaaaaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 7.3402458 s