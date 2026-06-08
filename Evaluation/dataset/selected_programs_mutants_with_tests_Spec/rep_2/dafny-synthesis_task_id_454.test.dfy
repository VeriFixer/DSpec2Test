
method {:test} Test3() {
var r0 := ContainsZ("z");
expect r0 <==> exists i :: 0 <= i < |"z"| && ("z"[i] == 'z' || "z"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'Z');
}

// REPEAT 2 - TIME: 5.4682473 s