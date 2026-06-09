
method {:test} Test6() {
var r0 := CountCharacters("\U{0002}\0aaaaaaaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaaaaaaaaaaa\U{0004}"|;
}

// REPEAT 7 - TIME: 6.1867375 s