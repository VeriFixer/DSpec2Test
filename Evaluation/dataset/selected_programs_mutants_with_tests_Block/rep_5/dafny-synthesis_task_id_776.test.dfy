
method {:test} Test4() {
var r0 := CountVowelNeighbors("\U{0004}aa\0aaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.0786955 s