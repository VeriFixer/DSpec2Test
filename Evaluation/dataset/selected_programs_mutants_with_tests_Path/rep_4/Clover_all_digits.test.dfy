
method {:test} Test6() {
var r0 := allDigits("99aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a9");
expect r0 <==> forall i :: 0 <= i < |"99aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a9"| ==> "99aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a9"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("\0aa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}"| ==> "\0aa\U{0002}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 35.1137047 s