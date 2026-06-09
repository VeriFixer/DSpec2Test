
method {:test} Test2() {
var r0 := RemoveChars("\U{0002}a\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect |r0| <= |"\U{0002}a\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}a\U{0002}" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect forall i :: 0 <= i < |"\U{0002}a\U{0002}"| ==> "\U{0002}a\U{0002}"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" || "\U{0002}a\U{0002}"[i] in r0;
}
method {:test} Test3() {
var r0 := RemoveChars("\U{0004}\0", "aaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\U{0004}\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\0" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"\U{0004}\0"| ==> "\U{0004}\0"[i] in "aaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\U{0002}" || "\U{0004}\0"[i] in r0;
}

// REPEAT 2 - TIME: 3.7538359 s