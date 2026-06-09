
method {:test} Test6() {
var r0 := ContainsZ("\U{0001}aZaaaaaaaaaaaaa\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}aZaaaaaaaaaaaaa\U{0003}"| && ("\U{0001}aZaaaaaaaaaaaaa\U{0003}"[i] == 'z' || "\U{0001}aZaaaaaaaaaaaaa\U{0003}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0001}za\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}za\U{0003}"| && ("\U{0001}za\U{0003}"[i] == 'z' || "\U{0001}za\U{0003}"[i] == 'Z');
}

// REPEAT 4 - TIME: 6.9118352 s