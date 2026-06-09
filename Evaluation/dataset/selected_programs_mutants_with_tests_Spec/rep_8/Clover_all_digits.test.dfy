
method {:test} Test14() {
var r0 := allDigits("12aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aa");
expect r0 <==> forall i :: 0 <= i < |"12aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aa"| ==> "12aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aa"[i] in "0123456789";
}
method {:test} Test15() {
var r0 := allDigits("\U{0004}\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}\0"| ==> "\U{0004}\U{0002}\0"[i] in "0123456789";
}

// REPEAT 8 - TIME: 14.5119772 s