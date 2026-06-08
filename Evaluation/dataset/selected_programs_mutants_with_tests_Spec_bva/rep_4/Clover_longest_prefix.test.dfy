
method {:test} Test42() {
var r0 := LongestCommonPrefix("\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}", "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}");
expect |r0| <= |"\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}"| && r0 == "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}"[0 .. |r0|] && |r0| <= |"\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}"| && r0 == "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}"[0 .. |r0|];
expect |r0| == |"\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}"| || |r0| == |"\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}"| || "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}"[|r0|] != "\U{0002}a\naa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\0\U{0004}"[|r0|];
}
method {:test} Test43() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaaa\0", "\U{0002}aaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaa\0"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaa\0"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaa\0"| || |r0| == |"\U{0002}aaaaaaaaaaaaaaaaa"| || "\U{0002}aaaaaaaaaaaaaaaaa\0"[|r0|] != "\U{0002}aaaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test44() {
var r0 := LongestCommonPrefix("\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa", "\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"| || "\U{0008}\0aaa\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\U{0008}\U{0002}a\naaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|];
}

// REPEAT 4 - TIME: 20.4025891 s