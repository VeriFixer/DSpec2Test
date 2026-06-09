
method {:test} Test36() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| || "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[|r0|];
}
method {:test} Test37() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"| || |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[|r0|] != "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa"[|r0|];
}
method {:test} Test38() {
var r0 := LongestCommonPrefix("\0\U{0002}", "\0\U{0004}");
expect |r0| <= |"\0\U{0002}"| && r0 == "\0\U{0002}"[0 .. |r0|] && |r0| <= |"\0\U{0004}"| && r0 == "\0\U{0004}"[0 .. |r0|];
expect |r0| == |"\0\U{0002}"| || |r0| == |"\0\U{0004}"| || "\0\U{0002}"[|r0|] != "\0\U{0004}"[|r0|];
}

// REPEAT 2 - TIME: 13.3620071 s