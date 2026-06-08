
method {:test} Test39() {
var r0 := LongestCommonPrefix("\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n", "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}");
expect |r0| <= |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"| && r0 == "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[0 .. |r0|] && |r0| <= |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"| && r0 == "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"| || |r0| == |"\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"| || "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\n"[|r0|] != "\U{0008}a\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0004}\U{000C}\U{0006}"[|r0|];
}
method {:test} Test40() {
var r0 := LongestCommonPrefix("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa");
expect |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"| && r0 == "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"| || |r0| == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"| || "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa\U{0002}"[|r0|] != "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaa"[|r0|];
}
method {:test} Test41() {
var r0 := LongestCommonPrefix("\U{0002}\U{0004}\0", "\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}\U{0004}\0"| && r0 == "\U{0002}\U{0004}\0"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\U{0004}\0"| || |r0| == |"\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0002}\U{0004}\0"[|r0|] != "\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 3 - TIME: 18.1902707 s