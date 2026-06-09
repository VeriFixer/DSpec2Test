
method {:test} Test8() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 9 - TIME: 8.3663277 s