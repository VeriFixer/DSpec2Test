
method {:test} Test12() {
var r0 := allDigits("3452aaaaaaaaaaaaaaaaaaaaa0aaaaaaa1aaaa");
expect r0 <==> forall i :: 0 <= i < |"3452aaaaaaaaaaaaaaaaaaaaa0aaaaaaa1aaaa"| ==> "3452aaaaaaaaaaaaaaaaaaaaa0aaaaaaa1aaaa"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("a\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0008}a\U{0004}\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0008}a\U{0004}\U{0006}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0008}a\U{0004}\U{0006}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 12.920493 s