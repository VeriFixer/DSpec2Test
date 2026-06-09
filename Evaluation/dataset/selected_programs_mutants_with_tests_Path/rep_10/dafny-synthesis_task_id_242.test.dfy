
method {:test} Test9() {
var r0 := CountCharacters("\U{0004}\0a\U{0002}aaaaaaa\U{0006}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0a\U{0002}aaaaaaa\U{0006}"|;
}

// REPEAT 10 - TIME: 13.4232644 s