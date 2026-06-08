
method {:test} Test11() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 5 - TIME: 9.8213424 s