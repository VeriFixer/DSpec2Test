
method {:test} Test15() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\0aaaaaaaaaa\U{0004}aaa");
expect r0 >= 0;
}
method {:test} Test16() {
var r0 := CountVowelNeighbors("\na\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}aa\0aa\U{0002}aaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountVowelNeighbors("aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0002}\0aaaa\U{0004}aaaaa");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountVowelNeighbors("\U{0008}aaaa\naaaaaaaaaaaa\0aaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaaaaa\U{0006}aa");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 37.1840065 s