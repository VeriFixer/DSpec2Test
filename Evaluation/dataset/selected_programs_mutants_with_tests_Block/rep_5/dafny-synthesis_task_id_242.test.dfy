
method {:test} Test4() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 5 - TIME: 4.974898 s