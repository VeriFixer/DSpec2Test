
method {:test} Test27() {
var r0 := allDigits("30");
expect r0 <==> forall i :: 0 <= i < |"30"| ==> "30"[i] in "0123456789";
}
method {:test} Test28() {
var r0 := allDigits("\U{0002}aa\U{0006}a\U{0004}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aa\U{0006}a\U{0004}\0"| ==> "\U{0002}aa\U{0006}a\U{0004}\0"[i] in "0123456789";
}

// REPEAT 8 - TIME: 20.0411078 s