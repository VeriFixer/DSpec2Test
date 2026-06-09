
method {:test} Test6() {
var r0 := LongestCommonPrefix("\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa", "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}");
expect |r0| <= |"\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa"| && r0 == "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}"| && r0 == "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}"[0 .. |r0|];
expect |r0| == |"\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa"| || |r0| == |"\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}"| || "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa"[|r0|] != "\naaaaaaaaaa\0aa\U{0002}aaaaaaaaa\U{0004}a\U{0008}aaaaaaaaaa\U{0006}"[|r0|];
}
method {:test} Test7() {
var r0 := LongestCommonPrefix("\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}", "\n\0aaa");
expect |r0| <= |"\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}"| && r0 == "\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}"[0 .. |r0|] && |r0| <= |"\n\0aaa"| && r0 == "\n\0aaa"[0 .. |r0|];
expect |r0| == |"\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}"| || |r0| == |"\n\0aaa"| || "\n\0aaaaaaaaa\U{0002}aa\U{0004}aaaaaaaaa\U{0006}a\U{0008}"[|r0|] != "\n\0aaa"[|r0|];
}
method {:test} Test8() {
var r0 := LongestCommonPrefix("\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}", "\U{0004}\U{0008}\0");
expect |r0| <= |"\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}"| && r0 == "\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}"[0 .. |r0|] && |r0| <= |"\U{0004}\U{0008}\0"| && r0 == "\U{0004}\U{0008}\0"[0 .. |r0|];
expect |r0| == |"\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}"| || |r0| == |"\U{0004}\U{0008}\0"| || "\U{0004}\U{0006}aaaaaaaaaaaaaaaa\U{0002}"[|r0|] != "\U{0004}\U{0008}\0"[|r0|];
}

// REPEAT 3 - TIME: 6.7084927 s