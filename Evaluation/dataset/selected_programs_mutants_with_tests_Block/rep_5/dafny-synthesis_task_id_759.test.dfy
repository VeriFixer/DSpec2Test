
method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}.\U{0003}a"| && "\U{0001}.\U{0003}a"[i] == '.' && |"\U{0001}.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}.\U{0003}a"| && "\U{0001}.\U{0003}a"[i] == '.' && |"\U{0001}.\U{0003}a"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 8.8088024 s