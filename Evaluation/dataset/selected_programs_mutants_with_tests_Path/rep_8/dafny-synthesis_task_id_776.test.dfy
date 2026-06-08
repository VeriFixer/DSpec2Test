
method {:test} Test35() {
var r0 := CountVowelNeighbors("a\U{0001}a");
expect r0 >= 0;
}
method {:test} Test36() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountVowelNeighbors("a\0a\U{0001}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 92.7547095 s