
method {:test} Test18() {
var r0 := allDigits("99a9aaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaaaaa9a9999");
expect r0 <==> forall i :: 0 <= i < |"99a9aaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaaaaa9a9999"| ==> "99a9aaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaaaaa9a9999"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\0aaaaa");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaa"| ==> "\0aaaaa"[i] in "0123456789";
}

// REPEAT 10 - TIME: 67.980341 s