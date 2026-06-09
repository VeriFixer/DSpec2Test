
method {:test} Test16() {
var r0 := CountVowelNeighbors("\na\0\U{0004}a\U{0006}\U{0002}\U{0008}");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 11.661129 s