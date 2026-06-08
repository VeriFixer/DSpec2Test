
method {:test} Test14() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test15() {
var r0 := LongestCommonPrefix("\0aaa\U{0006}aaaaa", "\U{0002}aaaa\U{0004}aaaa");
expect |r0| <= |"\0aaa\U{0006}aaaaa"| && r0 == "\0aaa\U{0006}aaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaa\U{0004}aaaa"| && r0 == "\U{0002}aaaa\U{0004}aaaa"[0 .. |r0|];
expect |r0| == |"\0aaa\U{0006}aaaaa"| || |r0| == |"\U{0002}aaaa\U{0004}aaaa"| || "\0aaa\U{0006}aaaaa"[|r0|] != "\U{0002}aaaa\U{0004}aaaa"[|r0|];
}

// REPEAT 8 - TIME: 11.3650293 s