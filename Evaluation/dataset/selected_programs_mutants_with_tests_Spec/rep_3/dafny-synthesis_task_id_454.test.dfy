
method {:test} Test6() {
var r0 := ContainsZ("z\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"z\U{0001}"| && ("z\U{0001}"[i] == 'z' || "z\U{0001}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("Z\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"Z\U{0001}"| && ("Z\U{0001}"[i] == 'z' || "Z\U{0001}"[i] == 'Z');
}
method {:test} Test8() {
var r0 := ContainsZ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| && ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'z' || "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'Z');
}

// REPEAT 3 - TIME: 7.8477008 s