
method {:test} Test30() {
var r0 := CountVowelNeighbors("aaa");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountVowelNeighbors("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a");
expect r0 >= 0;
}
method {:test} Test32() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 76.1706357 s