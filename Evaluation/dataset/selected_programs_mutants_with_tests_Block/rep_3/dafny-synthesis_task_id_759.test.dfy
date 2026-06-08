
method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.a\0"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '.' && |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '.' && |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 5.902959 s