
method {:test} Test7() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 8 - TIME: 7.8051941 s