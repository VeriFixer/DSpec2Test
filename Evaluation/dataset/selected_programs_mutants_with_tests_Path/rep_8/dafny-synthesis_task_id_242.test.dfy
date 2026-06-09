
method {:test} Test7() {
var r0 := CountCharacters("a\0aaaaa\U{0002}aaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"a\0aaaaa\U{0002}aaaaaaa\U{0004}"|;
}

// REPEAT 8 - TIME: 11.3233394 s