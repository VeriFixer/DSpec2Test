
method {:test} Test5() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaaaaaaaaa\0");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaa\0\U{0005}aaaaaaaaaaaa\U{0007}");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountVowelNeighbors("\taaaaaaaa\0aaaaaa\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaaaaaaaa\U{0007}");
expect r0 >= 0;
}
method {:test} Test8() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0005}aaaaaa\U{0003}aaaaaaa\U{0007}");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 11.7643182 s