
method {:test} Test8() {
var r0 := CountCharacters("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 2 - TIME: 7.3307645 s