
method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && "\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '.' && |"\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && "\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '.' && |"\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}");
expect r0 ==> exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"| && "\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"| && "\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 11.7186797 s