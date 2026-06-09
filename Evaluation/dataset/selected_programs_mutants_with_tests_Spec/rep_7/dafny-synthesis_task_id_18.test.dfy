
method {:test} Test6() {
var r0 := RemoveChars("\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0008}\0a\U{0004}aaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\n");
expect |r0| <= |"\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}" && !(r0[i] in "\U{0008}\0a\U{0004}aaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\n");
expect forall i :: 0 <= i < |"\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}"| ==> "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}"[i] in "\U{0008}\0a\U{0004}aaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\n" || "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}"[i] in r0;
}

// REPEAT 7 - TIME: 8.4146037 s