
method {:test} Test12() {
var r0 := allDigits("18a0a");
expect r0 <==> forall i :: 0 <= i < |"18a0a"| ==> "18a0a"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("aaa\0a");
expect r0 <==> forall i :: 0 <= i < |"aaa\0a"| ==> "aaa\0a"[i] in "0123456789";
}

// REPEAT 7 - TIME: 45.1333623 s