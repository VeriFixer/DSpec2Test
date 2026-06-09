
method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\0a"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 4.2021944 s