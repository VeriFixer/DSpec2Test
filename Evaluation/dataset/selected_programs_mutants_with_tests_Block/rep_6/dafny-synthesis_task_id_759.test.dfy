
method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision(".\U{0001}a");
expect r0 ==> exists i :: 0 <= i < |".\U{0001}a"| && ".\U{0001}a"[i] == '.' && |".\U{0001}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".\U{0001}a"| && ".\U{0001}a"[i] == '.' && |".\U{0001}a"| - i - 1 == 2;
}
method {:test} Test11() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}\0a\U{0006}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}\0a\U{0006}\U{0002}"| && "\U{0004}\0a\U{0006}\U{0002}"[i] == '.' && |"\U{0004}\0a\U{0006}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}\0a\U{0006}\U{0002}"| && "\U{0004}\0a\U{0006}\U{0002}"[i] == '.' && |"\U{0004}\0a\U{0006}\U{0002}"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 10.395468 s