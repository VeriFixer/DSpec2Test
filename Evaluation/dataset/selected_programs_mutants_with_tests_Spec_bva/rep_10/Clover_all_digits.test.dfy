
method {:test} Test31() {
var r0 := allDigits("50");
expect r0 <==> forall i :: 0 <= i < |"50"| ==> "50"[i] in "0123456789";
}
method {:test} Test32() {
var r0 := allDigits("\n\U{0008}a\U{0004}a\0\U{0006}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\n\U{0008}a\U{0004}a\0\U{0006}\U{0002}"| ==> "\n\U{0008}a\U{0004}a\0\U{0006}\U{0002}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 22.9157262 s