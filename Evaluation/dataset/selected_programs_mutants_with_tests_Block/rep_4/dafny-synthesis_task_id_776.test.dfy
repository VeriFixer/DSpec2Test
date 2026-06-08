
method {:test} Test3() {
var r0 := CountVowelNeighbors("aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.1068572 s