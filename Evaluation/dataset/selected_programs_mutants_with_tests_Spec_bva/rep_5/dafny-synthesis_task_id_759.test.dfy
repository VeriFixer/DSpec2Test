
method {:test} Test20() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| && "aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"[i] == '.' && |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| && "aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"[i] == '.' && |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| - i - 1 == 2;
}
method {:test} Test21() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaa.a\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaa.a\U{0001}"| && "\U{0003}aaaaa.a\U{0001}"[i] == '.' && |"\U{0003}aaaaa.a\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaa.a\U{0001}"| && "\U{0003}aaaaa.a\U{0001}"[i] == '.' && |"\U{0003}aaaaa.a\U{0001}"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 13.1628717 s