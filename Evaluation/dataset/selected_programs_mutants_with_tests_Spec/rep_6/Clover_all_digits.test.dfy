
method {:test} Test10() {
var r0 := allDigits("345aaaa1aaaaaaaaaaaa0aaaaaaa2");
expect r0 <==> forall i :: 0 <= i < |"345aaaa1aaaaaaaaaaaa0aaaaaaa2"| ==> "345aaaa1aaaaaaaaaaaa0aaaaaaa2"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0006}\0aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}"| ==> "\U{0006}\0aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}"[i] in "0123456789";
}

// REPEAT 6 - TIME: 10.860564 s