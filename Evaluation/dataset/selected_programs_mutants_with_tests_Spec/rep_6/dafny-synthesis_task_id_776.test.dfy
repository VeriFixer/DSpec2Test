
method {:test} Test5() {
var r0 := CountVowelNeighbors("aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 8.2099049 s