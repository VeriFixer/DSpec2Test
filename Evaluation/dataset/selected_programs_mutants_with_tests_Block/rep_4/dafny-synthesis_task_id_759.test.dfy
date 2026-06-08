
method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
expect r0 ==> exists i :: 0 <= i < |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| && "aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '.' && |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| && "aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '.' && |"aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 7.5247555 s