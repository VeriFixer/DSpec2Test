
method {:test} Test30() {
var r0 := IsDecimalWithTwoPrecision("aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| && "aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"[i] == '.' && |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| && "aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"[i] == '.' && |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| - i - 1 == 2;
}
method {:test} Test31() {
var r0 := IsDecimalWithTwoPrecision("aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| && "aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"[i] == '.' && |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| && "aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"[i] == '.' && |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 19.4102278 s