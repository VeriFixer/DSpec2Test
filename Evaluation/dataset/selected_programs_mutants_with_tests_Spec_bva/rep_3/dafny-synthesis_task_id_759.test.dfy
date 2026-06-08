
method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| && "\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"[i] == '.' && |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| && "\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"[i] == '.' && |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}\U{0001}.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}\U{0001}.\U{0003}a"| && "\U{0005}\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}\U{0001}.\U{0003}a"| && "\U{0005}\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}.\U{0003}a"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 10.9769213 s