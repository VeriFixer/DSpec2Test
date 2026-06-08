
method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}a.\0a");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}a.\0a"| && "\U{0002}a.\0a"[i] == '.' && |"\U{0002}a.\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}a.\0a"| && "\U{0002}a.\0a"[i] == '.' && |"\U{0002}a.\0a"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 14.7372233 s