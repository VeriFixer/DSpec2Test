
method {:test} Test10() {
var r0 := RemoveChars("aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n", "aaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaaaaaaaaa\0\U{0002}aa\naaaaa\U{0004}\U{0006}\U{0008}");
expect |r0| <= |"aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaaaaaaaaa\0\U{0002}aa\naaaaa\U{0004}\U{0006}\U{0008}");
expect forall i :: 0 <= i < |"aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"| ==> "aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[i] in "aaaaaaaaaaaaaaaaaaaaaa\U{000C}aaaaaaaaaaaa\0\U{0002}aa\naaaaa\U{0004}\U{0006}\U{0008}" || "aaa\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[i] in r0;
}
method {:test} Test11() {
var r0 := RemoveChars("\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa", "\U{0002}");
expect |r0| <= |"\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa" && !(r0[i] in "\U{0002}");
expect forall i :: 0 <= i < |"\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa"| ==> "\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa"[i] in "\U{0002}" || "\U{0002}\0aaa\U{0002}aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa"[i] in r0;
}

// REPEAT 6 - TIME: 9.9910132 s