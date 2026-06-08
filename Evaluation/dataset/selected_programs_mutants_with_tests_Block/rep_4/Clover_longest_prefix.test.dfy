
method {:test} Test6() {
var r0 := LongestCommonPrefix("\0aaaaa", "\0aaaaa");
expect |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|];
expect |r0| == |"\0aaaaa"| || |r0| == |"\0aaaaa"| || "\0aaaaa"[|r0|] != "\0aaaaa"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\U{0006}\0", "\U{0002}a\U{0004}");
expect |r0| <= |"\U{0006}\0"| && r0 == "\U{0006}\0"[0 .. |r0|] && |r0| <= |"\U{0002}a\U{0004}"| && r0 == "\U{0002}a\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0006}\0"| || |r0| == |"\U{0002}a\U{0004}"| || "\U{0006}\0"[|r0|] != "\U{0002}a\U{0004}"[|r0|];
}

// REPEAT 4 - TIME: 5.9537193 s