
method {:test} Test28() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"| - i - 1 == 2;
}
method {:test} Test29() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"| && "aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"[i] == '.' && |"aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"| && "aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"[i] == '.' && |"aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 18.9962631 s