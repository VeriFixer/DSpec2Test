
method {:test} Test9() {
var r0 := LongestCommonPrefix("\U{0002}\0", "\U{0002}\0");
expect |r0| <= |"\U{0002}\0"| && r0 == "\U{0002}\0"[0 .. |r0|] && |r0| <= |"\U{0002}\0"| && r0 == "\U{0002}\0"[0 .. |r0|];
expect |r0| == |"\U{0002}\0"| || |r0| == |"\U{0002}\0"| || "\U{0002}\0"[|r0|] != "\U{0002}\0"[|r0|];
}
method {:test} Test10() {
var r0 := LongestCommonPrefix("\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n", "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"| && r0 == "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"[0 .. |r0|] && |r0| <= |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"| && r0 == "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"| || |r0| == |"\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"| || "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa\U{0006}\U{0002}aaa\U{0008}\n"[|r0|] != "\U{000C}\0a\U{0004}aaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test11() {
var r0 := LongestCommonPrefix("\U{0006}\U{0004}a", "\U{0006}\0aaaa\U{0002}aaaa");
expect |r0| <= |"\U{0006}\U{0004}a"| && r0 == "\U{0006}\U{0004}a"[0 .. |r0|] && |r0| <= |"\U{0006}\0aaaa\U{0002}aaaa"| && r0 == "\U{0006}\0aaaa\U{0002}aaaa"[0 .. |r0|];
expect |r0| == |"\U{0006}\U{0004}a"| || |r0| == |"\U{0006}\0aaaa\U{0002}aaaa"| || "\U{0006}\U{0004}a"[|r0|] != "\U{0006}\0aaaa\U{0002}aaaa"[|r0|];
}

// REPEAT 4 - TIME: 10.0419318 s