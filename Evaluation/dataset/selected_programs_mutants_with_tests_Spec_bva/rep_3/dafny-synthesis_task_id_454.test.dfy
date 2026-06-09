
method {:test} Test25() {
var r0 := ContainsZ("\U{0003}az\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}az\U{0001}"| && ("\U{0003}az\U{0001}"[i] == 'z' || "\U{0003}az\U{0001}"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("aaZaa\U{0001}aaaaaaaaaa\U{0005}aaaa\U{0007}\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"aaZaa\U{0001}aaaaaaaaaa\U{0005}aaaa\U{0007}\U{0003}"| && ("aaZaa\U{0001}aaaaaaaaaa\U{0005}aaaa\U{0007}\U{0003}"[i] == 'z' || "aaZaa\U{0001}aaaaaaaaaa\U{0005}aaaa\U{0007}\U{0003}"[i] == 'Z');
}
method {:test} Test27() {
var r0 := ContainsZ("aaa\U{0006}\U{0004}aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}aaa\0\n");
expect r0 <==> exists i :: 0 <= i < |"aaa\U{0006}\U{0004}aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}aaa\0\n"| && ("aaa\U{0006}\U{0004}aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}aaa\0\n"[i] == 'z' || "aaa\U{0006}\U{0004}aaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}aaa\0\n"[i] == 'Z');
}

// REPEAT 3 - TIME: 14.4210403 s