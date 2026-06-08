
method {:test} Test26() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| && "aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"[i] == '.' && |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| && "aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"[i] == '.' && |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| - i - 1 == 2;
}
method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}.\U{0001}\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}.\U{0001}\U{0005}"| && "\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}.\U{0001}\U{0005}"| && "\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 17.5564168 s