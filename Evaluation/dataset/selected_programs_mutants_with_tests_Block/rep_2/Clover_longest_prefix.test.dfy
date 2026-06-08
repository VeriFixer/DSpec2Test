
method {:test} Test2() {
var r0 := LongestCommonPrefix("\0\U{0002}a", "\0aa");
expect |r0| <= |"\0\U{0002}a"| && r0 == "\0\U{0002}a"[0 .. |r0|] && |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}a"| || |r0| == |"\0aa"| || "\0\U{0002}a"[|r0|] != "\0aa"[|r0|];
}
method {:test} Test3() {
var r0 := LongestCommonPrefix("\U{0004}\U{0002}\0", "\U{0006}aaa");
expect |r0| <= |"\U{0004}\U{0002}\0"| && r0 == "\U{0004}\U{0002}\0"[0 .. |r0|] && |r0| <= |"\U{0006}aaa"| && r0 == "\U{0006}aaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0002}\0"| || |r0| == |"\U{0006}aaa"| || "\U{0004}\U{0002}\0"[|r0|] != "\U{0006}aaa"[|r0|];
}

// REPEAT 2 - TIME: 3.6523588 s