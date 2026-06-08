
method {:test} Test2() {
var r0 := allDigits("0");
expect r0 <==> forall i :: 0 <= i < |"0"| ==> "0"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 4.2861653 s