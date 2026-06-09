
method {:test} Test27() {
var r0 := ContainsZ("\U{0005}aaa\U{0001}aaaaaaaaaaaaaazaaaaaaaaaaaaa\taaaa\ra\U{0003}\U{000B}a\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaa\U{0001}aaaaaaaaaaaaaazaaaaaaaaaaaaa\taaaa\ra\U{0003}\U{000B}a\U{0007}"| && ("\U{0005}aaa\U{0001}aaaaaaaaaaaaaazaaaaaaaaaaaaa\taaaa\ra\U{0003}\U{000B}a\U{0007}"[i] == 'z' || "\U{0005}aaa\U{0001}aaaaaaaaaaaaaazaaaaaaaaaaaaa\taaaa\ra\U{0003}\U{000B}a\U{0007}"[i] == 'Z');
}
method {:test} Test28() {
var r0 := ContainsZ("\U{0006}aa\0aaaaaaaaaaaaaaaZaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aa\0aaaaaaaaaaaaaaaZaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa"| && ("\U{0006}aa\0aaaaaaaaaaaaaaaZaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa"[i] == 'z' || "\U{0006}aa\0aaaaaaaaaaaaaaaZaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa"[i] == 'Z');
}
method {:test} Test29() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa\U{0002}aaa\U{0004}a\U{0006}aa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa\U{0002}aaa\U{0004}a\U{0006}aa"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa\U{0002}aaa\U{0004}a\U{0006}aa"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa\U{0002}aaa\U{0004}a\U{0006}aa"[i] == 'Z');
}

// REPEAT 10 - TIME: 19.1086863 s