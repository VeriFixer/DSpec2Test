
method {:test} Test21() {
var r0 := RemoveChars("\U{0002}\U{0008}aaa\U{0008}", "\U{0004}\U{0008}\U{0002}a\0\U{0006}a");
expect |r0| <= |"\U{0002}\U{0008}aaa\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\U{0008}aaa\U{0008}" && !(r0[i] in "\U{0004}\U{0008}\U{0002}a\0\U{0006}a");
expect forall i :: 0 <= i < |"\U{0002}\U{0008}aaa\U{0008}"| ==> "\U{0002}\U{0008}aaa\U{0008}"[i] in "\U{0004}\U{0008}\U{0002}a\0\U{0006}a" || "\U{0002}\U{0008}aaa\U{0008}"[i] in r0;
}

// REPEAT 10 - TIME: 15.6958492 s