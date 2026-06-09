
method {:test} Test14() {
var r0 := RemoveChars("a\U{0002}a\U{0002}\0", "aaaa\0a");
expect |r0| <= |"a\U{0002}a\U{0002}\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\U{0002}a\U{0002}\0" && !(r0[i] in "aaaa\0a");
expect forall i :: 0 <= i < |"a\U{0002}a\U{0002}\0"| ==> "a\U{0002}a\U{0002}\0"[i] in "aaaa\0a" || "a\U{0002}a\U{0002}\0"[i] in r0;
}

// REPEAT 3 - TIME: 9.3751851 s