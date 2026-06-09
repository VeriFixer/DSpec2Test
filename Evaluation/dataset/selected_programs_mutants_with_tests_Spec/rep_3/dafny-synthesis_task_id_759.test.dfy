
method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("\0");
expect r0 ==> exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 5.5482751 s