
method {:test} Test12() {
var r0 := LongestCommonPrefix("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && r0 == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|];
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[|r0|];
}
method {:test} Test13() {
var r0 := LongestCommonPrefix("\0\U{0008}\U{0002}aaaa", "\U{0004}\U{0006}aaaaaa");
expect |r0| <= |"\0\U{0008}\U{0002}aaaa"| && r0 == "\0\U{0008}\U{0002}aaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0006}aaaaaa"| && r0 == "\U{0004}\U{0006}aaaaaa"[0 .. |r0|];
expect |r0| == |"\0\U{0008}\U{0002}aaaa"| || |r0| == |"\U{0004}\U{0006}aaaaaa"| || "\0\U{0008}\U{0002}aaaa"[|r0|] != "\U{0004}\U{0006}aaaaaa"[|r0|];
}

// REPEAT 7 - TIME: 10.0414874 s