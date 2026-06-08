
method {:test} Test10() {
var r0 := allDigits("132aaaaaaaaa0aaaaa");
expect r0 <==> forall i :: 0 <= i < |"132aaaaaaaaa0aaaaa"| ==> "132aaaaaaaaa0aaaaa"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a9a");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a9a"| ==> "\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a9a"[i] in "0123456789";
}

// REPEAT 6 - TIME: 53.4473023 s