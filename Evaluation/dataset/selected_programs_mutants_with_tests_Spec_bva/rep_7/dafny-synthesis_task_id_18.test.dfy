
method {:test} Test18() {
var r0 := RemoveChars("\0\0aaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0", "\U{0002}\0\U{0004}");
expect |r0| <= |"\0\0aaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0\0aaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0" && !(r0[i] in "\U{0002}\0\U{0004}");
expect forall i :: 0 <= i < |"\0\0aaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"| ==> "\0\0aaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"[i] in "\U{0002}\0\U{0004}" || "\0\0aaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\0"[i] in r0;
}

// REPEAT 7 - TIME: 12.1517508 s