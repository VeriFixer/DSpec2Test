
method {:test} Test8() {
var r0 := CountVowelNeighbors("\U{0002}\0aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 8.9155525 s