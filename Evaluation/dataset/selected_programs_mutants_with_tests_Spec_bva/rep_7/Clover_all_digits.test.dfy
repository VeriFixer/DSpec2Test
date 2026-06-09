
method {:test} Test25() {
var r0 := allDigits("24a0aaaaaaaaaaaaaaaaaaaaaaa1");
expect r0 <==> forall i :: 0 <= i < |"24a0aaaaaaaaaaaaaaaaaaaaaaa1"| ==> "24a0aaaaaaaaaaaaaaaaaaaaaaa1"[i] in "0123456789";
}
method {:test} Test26() {
var r0 := allDigits("\U{0004}a\U{0002}aa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}a\U{0002}aa\0"| ==> "\U{0004}a\U{0002}aa\0"[i] in "0123456789";
}

// REPEAT 7 - TIME: 16.4399066 s