
method {:test} Test6() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 7 - TIME: 7.16293 s