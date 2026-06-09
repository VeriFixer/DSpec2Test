
method {:test} Test21() {
var r0 := ContainsZ("\U{0005}\U{0003}\U{0001}z\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}\U{0003}\U{0001}z\U{0007}"| && ("\U{0005}\U{0003}\U{0001}z\U{0007}"[i] == 'z' || "\U{0005}\U{0003}\U{0001}z\U{0007}"[i] == 'Z');
}
method {:test} Test22() {
var r0 := ContainsZ("\U{0002}aaaaaa\0a\U{0008}aaaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaaaaaaaZ\U{000C}\na");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaa\0a\U{0008}aaaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaaaaaaaZ\U{000C}\na"| && ("\U{0002}aaaaaa\0a\U{0008}aaaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaaaaaaaZ\U{000C}\na"[i] == 'z' || "\U{0002}aaaaaa\0a\U{0008}aaaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaaaaaaaZ\U{000C}\na"[i] == 'Z');
}
method {:test} Test23() {
var r0 := ContainsZ("\U{0004}aaaa\U{0008}aaaaa\0aaaaaaaaaaaaaa\U{0006}aaa\U{0002}aaaaaaa\n\U{000E}\U{0010}\U{000C}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}aaaa\U{0008}aaaaa\0aaaaaaaaaaaaaa\U{0006}aaa\U{0002}aaaaaaa\n\U{000E}\U{0010}\U{000C}"| && ("\U{0004}aaaa\U{0008}aaaaa\0aaaaaaaaaaaaaa\U{0006}aaa\U{0002}aaaaaaa\n\U{000E}\U{0010}\U{000C}"[i] == 'z' || "\U{0004}aaaa\U{0008}aaaaa\0aaaaaaaaaaaaaa\U{0006}aaa\U{0002}aaaaaaa\n\U{000E}\U{0010}\U{000C}"[i] == 'Z');
}

// REPEAT 8 - TIME: 15.2179115 s