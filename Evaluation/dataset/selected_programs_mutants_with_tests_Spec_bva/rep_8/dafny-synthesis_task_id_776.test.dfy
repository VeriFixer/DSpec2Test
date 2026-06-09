
method {:test} Test15() {
var r0 := CountVowelNeighbors("\naaaaaa\U{0006}\U{0004}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0a\U{0008}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 11.0186955 s