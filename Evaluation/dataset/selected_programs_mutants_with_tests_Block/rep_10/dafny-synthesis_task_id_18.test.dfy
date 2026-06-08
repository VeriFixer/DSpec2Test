
method {:test} Test18() {
var r0 := RemoveChars("aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0" && !(r0[i] in "\U{0004}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect forall i :: 0 <= i < |"aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "\U{0004}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0002}" || "aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in r0;
}
method {:test} Test19() {
var r0 := RemoveChars("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] in r0;
}

// REPEAT 10 - TIME: 16.4298553 s