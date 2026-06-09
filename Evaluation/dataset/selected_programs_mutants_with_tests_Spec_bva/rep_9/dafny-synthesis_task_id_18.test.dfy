
method {:test} Test20() {
var r0 := RemoveChars("\U{0006}\0aaa\U{0004}aaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa\0", "\0a\U{0004}\U{0006}\U{0002}");
expect |r0| <= |"\U{0006}\0aaa\U{0004}aaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0006}\0aaa\U{0004}aaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa\0" && !(r0[i] in "\0a\U{0004}\U{0006}\U{0002}");
expect forall i :: 0 <= i < |"\U{0006}\0aaa\U{0004}aaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa\0"| ==> "\U{0006}\0aaa\U{0004}aaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa\0"[i] in "\0a\U{0004}\U{0006}\U{0002}" || "\U{0006}\0aaa\U{0004}aaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaa\0"[i] in r0;
}

// REPEAT 9 - TIME: 13.550738 s