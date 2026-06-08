
method {:test} Test17() {
var r0 := RemoveChars("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0002}\0");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" && !(r0[i] in "\U{0002}\0");
expect forall i :: 0 <= i < |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "\U{0002}\0" || "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in r0;
}

// REPEAT 6 - TIME: 12.6303775 s