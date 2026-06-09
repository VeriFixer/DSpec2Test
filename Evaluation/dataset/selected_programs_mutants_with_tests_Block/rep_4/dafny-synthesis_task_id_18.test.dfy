
method {:test} Test6() {
var r0 := RemoveChars("\0aa\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0004}aaa\U{0006}aa\U{0008}aa\U{0002}");
expect |r0| <= |"\0aa\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0aa\U{0002}" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0004}aaa\U{0006}aa\U{0008}aa\U{0002}");
expect forall i :: 0 <= i < |"\0aa\U{0002}"| ==> "\0aa\U{0002}"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0004}aaa\U{0006}aa\U{0008}aa\U{0002}" || "\0aa\U{0002}"[i] in r0;
}
method {:test} Test7() {
var r0 := RemoveChars("aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}" && !(r0[i] in "a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall i :: 0 <= i < |"aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> "aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] in "a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || "aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] in r0;
}

// REPEAT 4 - TIME: 6.3545155 s