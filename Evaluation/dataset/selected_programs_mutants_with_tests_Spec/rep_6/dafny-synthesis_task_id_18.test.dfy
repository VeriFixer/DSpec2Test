
method {:test} Test5() {
var r0 := RemoveChars("\0\0a", "\U{0002}aa");
expect |r0| <= |"\0\0a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0\0a" && !(r0[i] in "\U{0002}aa");
expect forall i :: 0 <= i < |"\0\0a"| ==> "\0\0a"[i] in "\U{0002}aa" || "\0\0a"[i] in r0;
}

// REPEAT 6 - TIME: 7.6650649 s