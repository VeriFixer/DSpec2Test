
method {:test} Test4() {
var r0 := RemoveChars("\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0" && !(r0[i] in "\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "\U{0004}aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0002}" || "\0"[i] in r0;
}
method {:test} Test5() {
var r0 := RemoveChars("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}" && !(r0[i] in "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}"| ==> "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}"[i] in "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}" || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}"[i] in r0;
}

// REPEAT 3 - TIME: 5.2179217 s