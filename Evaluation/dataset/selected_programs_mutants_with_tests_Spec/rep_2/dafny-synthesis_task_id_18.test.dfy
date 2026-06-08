
method {:test} Test1() {
var r0 := RemoveChars("a\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\0");
expect |r0| <= |"a\U{0002}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "a\U{0002}" && !(r0[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\0");
expect forall i :: 0 <= i < |"a\U{0002}"| ==> "a\U{0002}"[i] in "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\0" || "a\U{0002}"[i] in r0;
}

// REPEAT 2 - TIME: 3.6806915 s