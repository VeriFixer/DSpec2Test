
method {:test} Test19() {
var r0 := RemoveChars("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0002}\0a\U{0004}");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" && !(r0[i] in "\U{0002}\0a\U{0004}");
expect forall i :: 0 <= i < |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "\U{0002}\0a\U{0004}" || "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in r0;
}

// REPEAT 8 - TIME: 12.8093942 s