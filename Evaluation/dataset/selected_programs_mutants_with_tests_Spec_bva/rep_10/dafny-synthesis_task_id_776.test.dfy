
method {:test} Test17() {
var r0 := CountVowelNeighbors("\naaa\0aa\U{0006}aaaaaaaaaa\U{0002}aaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaa\U{0008}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 12.2883783 s