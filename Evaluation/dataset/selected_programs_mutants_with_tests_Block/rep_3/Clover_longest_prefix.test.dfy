
method {:test} Test4() {
var r0 := LongestCommonPrefix("\0aaa", "\0aaaa");
expect |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|] && |r0| <= |"\0aaaa"| && r0 == "\0aaaa"[0 .. |r0|];
expect |r0| == |"\0aaa"| || |r0| == |"\0aaaa"| || "\0aaa"[|r0|] != "\0aaaa"[|r0|];
}
method {:test} Test5() {
var r0 := LongestCommonPrefix("\0\U{0004}", "\U{0002}a");
expect |r0| <= |"\0\U{0004}"| && r0 == "\0\U{0004}"[0 .. |r0|] && |r0| <= |"\U{0002}a"| && r0 == "\U{0002}a"[0 .. |r0|];
expect |r0| == |"\0\U{0004}"| || |r0| == |"\U{0002}a"| || "\0\U{0004}"[|r0|] != "\U{0002}a"[|r0|];
}

// REPEAT 3 - TIME: 4.7956334 s