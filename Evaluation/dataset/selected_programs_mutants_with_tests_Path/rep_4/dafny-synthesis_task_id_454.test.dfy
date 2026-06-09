
method {:test} Test9() {
var r0 := ContainsZ("\0aa");
expect r0 <==> exists i :: 0 <= i < |"\0aa"| && ("\0aa"[i] == 'z' || "\0aa"[i] == 'Z');
}
method {:test} Test10() {
var r0 := ContainsZ("\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}az\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}az\U{0001}"| && ("\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}az\U{0001}"[i] == 'z' || "\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}az\U{0001}"[i] == 'Z');
}

// REPEAT 4 - TIME: 123.0037761 s