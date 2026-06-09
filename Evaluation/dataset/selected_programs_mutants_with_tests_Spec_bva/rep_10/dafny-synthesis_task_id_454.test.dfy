
method {:test} Test46() {
var r0 := ContainsZ("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaa\U{0003}aaaaaaaaaaaazaa\U{0005}aaaa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaa\U{0001}aaaaaaaaaaa\U{0003}aaaaaaaaaaaazaa\U{0005}aaaa"| && ("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaa\U{0003}aaaaaaaaaaaazaa\U{0005}aaaa"[i] == 'z' || "aaaaaaaaaaaaa\U{0001}aaaaaaaaaaa\U{0003}aaaaaaaaaaaazaa\U{0005}aaaa"[i] == 'Z');
}
method {:test} Test47() {
var r0 := ContainsZ("\U{0003}aaa\U{0001}aZaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaa\U{0001}aZaa"| && ("\U{0003}aaa\U{0001}aZaa"[i] == 'z' || "\U{0003}aaa\U{0001}aZaa"[i] == 'Z');
}
method {:test} Test48() {
var r0 := ContainsZ("a\naaa\0aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}aaa\U{0008}aaa");
expect r0 <==> exists i :: 0 <= i < |"a\naaa\0aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}aaa\U{0008}aaa"| && ("a\naaa\0aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}aaa\U{0008}aaa"[i] == 'z' || "a\naaa\0aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaaaaaaa\U{0006}aaa\U{0008}aaa"[i] == 'Z');
}

// REPEAT 10 - TIME: 27.0464274 s