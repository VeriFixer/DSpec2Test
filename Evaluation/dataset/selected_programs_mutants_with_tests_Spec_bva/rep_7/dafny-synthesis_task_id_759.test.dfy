
method {:test} Test24() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"| && "aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"[i] == '.' && |"aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"| && "aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"[i] == '.' && |"aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"| - i - 1 == 2;
}
method {:test} Test25() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"| && "aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"[i] == '.' && |"aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"| && "aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"[i] == '.' && |"aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 16.1212195 s