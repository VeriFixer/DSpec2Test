
method {:test} Test21() {
var r0 := ContainsZ("aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0006}aaa\U{0004}a");
expect r0 <==> exists i :: 0 <= i < |"aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0006}aaa\U{0004}a"| && ("aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0006}aaa\U{0004}a"[i] == 'z' || "aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0006}aaa\U{0004}a"[i] == 'Z');
}
method {:test} Test22() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZaaaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZaaaaaaaa"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZaaaaaaaa"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZaaaaaaaa"[i] == 'Z');
}

// REPEAT 8 - TIME: 474.5693697 s