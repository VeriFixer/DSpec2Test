
method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}aaaaaaa\t\U{000B}aa.\U{0003}\U{0001}"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"| && "\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"| && "\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaaa\U{0004}\U{0006}\na\U{0008}aaaaaaaaaa\0aa"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 14.387657 s