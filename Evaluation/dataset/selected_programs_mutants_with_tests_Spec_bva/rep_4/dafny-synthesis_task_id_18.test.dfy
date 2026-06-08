
method {:test} Test15() {
var r0 := RemoveChars("\0\0", "\U{0002}\0a");
expect |r0| <= |"\0\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0\0" && !(r0[i] in "\U{0002}\0a");
expect forall i :: 0 <= i < |"\0\0"| ==> "\0\0"[i] in "\U{0002}\0a" || "\0\0"[i] in r0;
}

// REPEAT 4 - TIME: 10.7169906 s