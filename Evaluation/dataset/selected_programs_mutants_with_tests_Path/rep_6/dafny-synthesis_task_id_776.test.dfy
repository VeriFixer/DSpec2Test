
method {:test} Test25() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountVowelNeighbors("aaa\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountVowelNeighbors("aaaaaaa\0aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test28() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 61.1548466 s