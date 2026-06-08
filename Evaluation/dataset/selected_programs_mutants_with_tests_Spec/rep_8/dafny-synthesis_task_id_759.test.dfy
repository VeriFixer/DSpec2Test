
method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && "\U{0004}\0\U{0002}"[i] == '.' && |"\U{0004}\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && "\U{0004}\0\U{0002}"[i] == '.' && |"\U{0004}\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}aa.\U{0001}\U{0003}");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}aa.\U{0001}\U{0003}"| && "\U{0005}aa.\U{0001}\U{0003}"[i] == '.' && |"\U{0005}aa.\U{0001}\U{0003}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}aa.\U{0001}\U{0003}"| && "\U{0005}aa.\U{0001}\U{0003}"[i] == '.' && |"\U{0005}aa.\U{0001}\U{0003}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 12.9241629 s