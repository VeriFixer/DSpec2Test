
method {:test} Test1() {
var r0 := CountVowelNeighbors("\U{0001}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.6291112 s