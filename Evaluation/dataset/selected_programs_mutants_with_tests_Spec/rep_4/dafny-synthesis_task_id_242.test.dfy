
method {:test} Test3() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 4 - TIME: 4.9885919 s