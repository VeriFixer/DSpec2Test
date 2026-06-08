
method {:test} Test15() {
var r0 := LongestCommonPrefix("\0aaa", "\0aaa");
expect |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|] && |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|];
expect |r0| == |"\0aaa"| || |r0| == |"\0aaa"| || "\0aaa"[|r0|] != "\0aaa"[|r0|];
}
method {:test} Test16() {
var r0 := LongestCommonPrefix("\0aaaaaa", "\0aaa");
expect |r0| <= |"\0aaaaaa"| && r0 == "\0aaaaaa"[0 .. |r0|] && |r0| <= |"\0aaa"| && r0 == "\0aaa"[0 .. |r0|];
expect |r0| == |"\0aaaaaa"| || |r0| == |"\0aaa"| || "\0aaaaaa"[|r0|] != "\0aaa"[|r0|];
}
method {:test} Test17() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaa", "\U{0004}\U{0002}aa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aa"| && r0 == "\U{0004}\U{0002}aa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aa"| || "\U{0004}\0aaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aa"[|r0|];
}

// REPEAT 6 - TIME: 14.4265224 s