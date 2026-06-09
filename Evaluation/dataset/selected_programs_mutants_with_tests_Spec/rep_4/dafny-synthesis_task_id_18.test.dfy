
method {:test} Test3() {
var r0 := RemoveChars("\U{0002}a", "a\0");
expect |r0| <= |"\U{0002}a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}a" && !(r0[i] in "a\0");
expect forall i :: 0 <= i < |"\U{0002}a"| ==> "\U{0002}a"[i] in "a\0" || "\U{0002}a"[i] in r0;
}

// REPEAT 4 - TIME: 5.8104375 s