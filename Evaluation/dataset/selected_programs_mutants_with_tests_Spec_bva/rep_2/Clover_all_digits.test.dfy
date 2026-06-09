
method {:test} Test15() {
var r0 := allDigits("09aa");
expect r0 <==> forall i :: 0 <= i < |"09aa"| ==> "09aa"[i] in "0123456789";
}
method {:test} Test16() {
var r0 := allDigits("\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 10.0796921 s