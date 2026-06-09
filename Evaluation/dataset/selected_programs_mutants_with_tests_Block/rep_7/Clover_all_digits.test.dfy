
method {:test} Test6() {
var r0 := allDigits("\U{0001}aa9aaaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t");
expect r0 <==> forall i :: 0 <= i < |"\U{0001}aa9aaaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t"| ==> "\U{0001}aa9aaaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t"[i] in "0123456789";
}

// REPEAT 7 - TIME: 6.4295425 s