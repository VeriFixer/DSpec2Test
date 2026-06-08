
method {:test} Test21() {
var r0 := allDigits("10");
expect r0 <==> forall i :: 0 <= i < |"10"| ==> "10"[i] in "0123456789";
}
method {:test} Test22() {
var r0 := allDigits("\U{0002}\0\U{0004}\U{0008}\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0\U{0004}\U{0008}\U{0006}"| ==> "\U{0002}\0\U{0004}\U{0008}\U{0006}"[i] in "0123456789";
}

// REPEAT 5 - TIME: 15.1118517 s