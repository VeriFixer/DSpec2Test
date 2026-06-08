
method {:test} Test12() {
var r0 := ContainsZ("\U{0004}a\0Za\U{0002}aaaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\0Za\U{0002}aaaaaa"| && ("\U{0004}a\0Za\U{0002}aaaaaa"[i] == 'z' || "\U{0004}a\0Za\U{0002}aaaaaa"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("\0\U{0002}za\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\0\U{0002}za\U{0004}"| && ("\0\U{0002}za\U{0004}"[i] == 'z' || "\0\U{0002}za\U{0004}"[i] == 'Z');
}

// REPEAT 7 - TIME: 11.4879742 s