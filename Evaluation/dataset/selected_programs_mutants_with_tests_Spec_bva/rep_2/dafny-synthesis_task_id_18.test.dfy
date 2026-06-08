
method {:test} Test13() {
var r0 := RemoveChars("aa\0", "\U{0002}\0");
expect |r0| <= |"aa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aa\0" && !(r0[i] in "\U{0002}\0");
expect forall i :: 0 <= i < |"aa\0"| ==> "aa\0"[i] in "\U{0002}\0" || "aa\0"[i] in r0;
}

// REPEAT 2 - TIME: 8.9620514 s