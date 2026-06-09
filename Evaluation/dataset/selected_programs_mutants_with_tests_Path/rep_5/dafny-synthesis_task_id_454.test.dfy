
method {:test} Test12() {
var r0 := ContainsZ("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}"| && ("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}"[i] == 'z' || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'Z');
}

// REPEAT 5 - TIME: 190.0620177 s