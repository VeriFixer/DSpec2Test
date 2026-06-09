
method {:test} Test45() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test46() {
var r0 := CountVowelNeighbors("a\U{0001}\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test47() {
var r0 := CountVowelNeighbors("\U{0005}\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test48() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test49() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 86.6302007 s