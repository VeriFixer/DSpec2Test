
method {:test} Test19() {
var r0 := allDigits("235a4aaaaaaaaaaa1aaaaaaaa0");
expect r0 <==> forall i :: 0 <= i < |"235a4aaaaaaaaaaa1aaaaaaaa0"| ==> "235a4aaaaaaaaaaa1aaaaaaaa0"[i] in "0123456789";
}
method {:test} Test20() {
var r0 := allDigits("\U{0002}\0\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0\U{0004}"| ==> "\U{0002}\0\U{0004}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 12.4637725 s