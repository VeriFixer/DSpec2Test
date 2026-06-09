
method {:test} Test2() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| && ("aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == 'z' || "aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == 'Z');
}
method {:test} Test3() {
var r0 := ContainsZ("aaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaz"| && ("aaaaaz"[i] == 'z' || "aaaaaz"[i] == 'Z');
}

// REPEAT 2 - TIME: 4.169998 s