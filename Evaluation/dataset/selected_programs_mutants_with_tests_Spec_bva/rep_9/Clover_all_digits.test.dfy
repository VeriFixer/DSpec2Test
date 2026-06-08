
method {:test} Test29() {
var r0 := allDigits("410");
expect r0 <==> forall i :: 0 <= i < |"410"| ==> "410"[i] in "0123456789";
}
method {:test} Test30() {
var r0 := allDigits("\U{000C}\0aaa\U{0006}a\U{0008}aaa\U{000E}a\U{0004}aaaaaaa\U{0002}aaaa\n");
expect r0 <==> forall i :: 0 <= i < |"\U{000C}\0aaa\U{0006}a\U{0008}aaa\U{000E}a\U{0004}aaaaaaa\U{0002}aaaa\n"| ==> "\U{000C}\0aaa\U{0006}a\U{0008}aaa\U{000E}a\U{0004}aaaaaaa\U{0002}aaaa\n"[i] in "0123456789";
}

// REPEAT 9 - TIME: 21.3307645 s