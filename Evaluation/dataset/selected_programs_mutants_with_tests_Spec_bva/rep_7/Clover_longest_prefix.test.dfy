
method {:test} Test51() {
var r0 := LongestCommonPrefix("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa");
expect |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa"[0 .. |r0|] && |r0| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa"| && r0 == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa"[0 .. |r0|];
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa"| || |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa"| || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa"[|r0|] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa\U{0002}\U{0006}aaa\U{0008}\0aa"[|r0|];
}
method {:test} Test52() {
var r0 := LongestCommonPrefix("\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa", "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa");
expect |r0| <= |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa"| && r0 == "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa"| || |r0| == |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa"| || "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaaa"[|r0|] != "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa"[|r0|];
}
method {:test} Test53() {
var r0 := LongestCommonPrefix("\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0002}\0a\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0002}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 7 - TIME: 18.5322332 s