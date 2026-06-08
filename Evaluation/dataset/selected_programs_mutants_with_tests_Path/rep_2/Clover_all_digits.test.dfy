
method {:test} Test2() {
var r0 := allDigits("a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0");
expect r0 <==> forall i :: 0 <= i < |"a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"| ==> "a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("a\0");
expect r0 <==> forall i :: 0 <= i < |"a\0"| ==> "a\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 18.976511 s