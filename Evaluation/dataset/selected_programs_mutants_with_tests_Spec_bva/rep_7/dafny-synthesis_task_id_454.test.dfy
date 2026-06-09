
method {:test} Test37() {
var r0 := ContainsZ("\U{0001}aaz\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}aaz\U{0003}"| && ("\U{0001}aaz\U{0003}"[i] == 'z' || "\U{0001}aaz\U{0003}"[i] == 'Z');
}
method {:test} Test38() {
var r0 := ContainsZ("\U{0007}aaaaaaaaaaaZaaaaaaaaaa\U{0003}\U{0005}\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaZaaaaaaaaaa\U{0003}\U{0005}\U{0001}"| && ("\U{0007}aaaaaaaaaaaZaaaaaaaaaa\U{0003}\U{0005}\U{0001}"[i] == 'z' || "\U{0007}aaaaaaaaaaaZaaaaaaaaaa\U{0003}\U{0005}\U{0001}"[i] == 'Z');
}
method {:test} Test39() {
var r0 := ContainsZ("aa\n\U{0008}a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"aa\n\U{0008}a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"| && ("aa\n\U{0008}a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"[i] == 'z' || "aa\n\U{0008}a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaa\U{0006}"[i] == 'Z');
}

// REPEAT 7 - TIME: 21.1931653 s