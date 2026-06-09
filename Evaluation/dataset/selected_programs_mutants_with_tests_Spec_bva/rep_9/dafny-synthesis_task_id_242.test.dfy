
method {:test} Test15() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 9 - TIME: 11.9672335 s