
method {:test} Test57() {
var r0 := LongestCommonPrefix("\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test58() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| || |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"[|r0|] != "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test59() {
var r0 := LongestCommonPrefix("a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa", "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa"| || "a\0aaaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 9 - TIME: 31.7075999 s