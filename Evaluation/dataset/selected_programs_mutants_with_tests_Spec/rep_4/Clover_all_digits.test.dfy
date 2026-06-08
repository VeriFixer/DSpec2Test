
method {:test} Test6() {
var r0 := allDigits("3aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1aa0a2");
expect r0 <==> forall i :: 0 <= i < |"3aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1aa0a2"| ==> "3aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1aa0a2"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a");
expect r0 <==> forall i :: 0 <= i < |"a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"| ==> "a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"[i] in "0123456789";
}

// REPEAT 4 - TIME: 7.8174913 s