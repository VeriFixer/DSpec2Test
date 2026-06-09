
method {:test} Test16() {
var r0 := allDigits("0324aaaaaaaaaaaaaaaaaaaaaa1");
expect r0 <==> forall i :: 0 <= i < |"0324aaaaaaaaaaaaaaaaaaaaaa1"| ==> "0324aaaaaaaaaaaaaaaaaaaaaa1"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\U{0004}\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}\0"| ==> "\U{0004}\U{0002}\0"[i] in "0123456789";
}

// REPEAT 9 - TIME: 16.6135229 s