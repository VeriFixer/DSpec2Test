
method {:test} Test13() {
var r0 := CountCharacters("\U{0006}\0\U{0004}\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0006}\0\U{0004}\U{0002}"|;
}

// REPEAT 7 - TIME: 10.6420222 s