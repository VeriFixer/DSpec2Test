
method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("a\0\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"a\0\U{0004}\U{0002}"| && "a\0\U{0004}\U{0002}"[i] == '.' && |"a\0\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\0\U{0004}\U{0002}"| && "a\0\U{0004}\U{0002}"[i] == '.' && |"a\0\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test11() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaa.\U{0001}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaa.\U{0001}a"| && "\U{0003}aaaaa.\U{0001}a"[i] == '.' && |"\U{0003}aaaaa.\U{0001}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaa.\U{0001}a"| && "\U{0003}aaaaa.\U{0001}a"[i] == '.' && |"\U{0003}aaaaa.\U{0001}a"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 10.5505359 s