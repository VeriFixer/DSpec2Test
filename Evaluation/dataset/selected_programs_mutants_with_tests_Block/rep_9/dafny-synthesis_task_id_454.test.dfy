
method {:test} Test16() {
var r0 := ContainsZ("Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa"| && ("Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa"[i] == 'z' || "Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa"| && ("\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa"[i] == 'z' || "\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa"[i] == 'Z');
}

// REPEAT 9 - TIME: 13.3181717 s