
method {:test} Test23() {
var r0 := allDigits("310");
expect r0 <==> forall i :: 0 <= i < |"310"| ==> "310"[i] in "0123456789";
}
method {:test} Test24() {
var r0 := allDigits("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 6 - TIME: 16.5367221 s