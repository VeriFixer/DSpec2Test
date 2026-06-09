
method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0005}\0aaa\U{0007}aaaaaaaaaa\U{0003}aa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 9.5045183 s