
method {:test} Test7() {
var r0 := RemoveChars("\U{0002}\U{0002}a", "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| <= |"\U{0002}\U{0002}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\U{0002}a" && !(r0[i] in "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect forall i :: 0 <= i < |"\U{0002}\U{0002}a"| ==> "\U{0002}\U{0002}a"[i] in "\U{0006}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}" || "\U{0002}\U{0002}a"[i] in r0;
}

// REPEAT 8 - TIME: 9.4395224 s