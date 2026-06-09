
method {:test} Test14() {
var r0 := ContainsZ("aaaaa\U{0004}aaaaa\U{0008}aaaaa\na\U{000C}\U{000E}aaa\U{0012}\U{0010}aa\0aaaaaaaaaZa\U{0006}aa\U{0002}aaaaa\U{0014}");
expect r0 <==> exists i :: 0 <= i < |"aaaaa\U{0004}aaaaa\U{0008}aaaaa\na\U{000C}\U{000E}aaa\U{0012}\U{0010}aa\0aaaaaaaaaZa\U{0006}aa\U{0002}aaaaa\U{0014}"| && ("aaaaa\U{0004}aaaaa\U{0008}aaaaa\na\U{000C}\U{000E}aaa\U{0012}\U{0010}aa\0aaaaaaaaaZa\U{0006}aa\U{0002}aaaaa\U{0014}"[i] == 'z' || "aaaaa\U{0004}aaaaa\U{0008}aaaaa\na\U{000C}\U{000E}aaa\U{0012}\U{0010}aa\0aaaaaaaaaZa\U{0006}aa\U{0002}aaaaa\U{0014}"[i] == 'Z');
}
method {:test} Test15() {
var r0 := ContainsZ("\U{0002}\0z");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0z"| && ("\U{0002}\0z"[i] == 'z' || "\U{0002}\0z"[i] == 'Z');
}

// REPEAT 8 - TIME: 12.1623788 s