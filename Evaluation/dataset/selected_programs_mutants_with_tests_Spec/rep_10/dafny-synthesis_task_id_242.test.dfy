
method {:test} Test9() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 10 - TIME: 9.021176 s