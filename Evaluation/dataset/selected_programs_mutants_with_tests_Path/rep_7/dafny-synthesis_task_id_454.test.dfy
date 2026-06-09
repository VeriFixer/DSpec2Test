
method {:test} Test18() {
var r0 := ContainsZ("\U{000C}a\U{0004}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0008}\n");
expect r0 <==> exists i :: 0 <= i < |"\U{000C}a\U{0004}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0008}\n"| && ("\U{000C}a\U{0004}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0008}\n"[i] == 'z' || "\U{000C}a\U{0004}aaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0008}\n"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}
method {:test} Test20() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'Z');
}

// REPEAT 7 - TIME: 374.939978 s