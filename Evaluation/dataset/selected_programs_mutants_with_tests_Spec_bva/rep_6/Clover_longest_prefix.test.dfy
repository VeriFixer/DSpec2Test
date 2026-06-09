
method {:test} Test48() {
var r0 := LongestCommonPrefix("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n", "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa");
expect |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n"[0 .. |r0|] && |r0| <= |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa"| && r0 == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa"[0 .. |r0|];
expect |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n"| || |r0| == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa"| || "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n"[|r0|] != "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaa\U{0008}a\U{0004}aaaa\n\U{000C}aa"[|r0|];
}
method {:test} Test49() {
var r0 := LongestCommonPrefix("\0a\U{0002}aa\U{0004}aa", "\0a\U{0002}aa\U{0004}a");
expect |r0| <= |"\0a\U{0002}aa\U{0004}aa"| && r0 == "\0a\U{0002}aa\U{0004}aa"[0 .. |r0|] && |r0| <= |"\0a\U{0002}aa\U{0004}a"| && r0 == "\0a\U{0002}aa\U{0004}a"[0 .. |r0|];
expect |r0| == |"\0a\U{0002}aa\U{0004}aa"| || |r0| == |"\0a\U{0002}aa\U{0004}a"| || "\0a\U{0002}aa\U{0004}aa"[|r0|] != "\0a\U{0002}aa\U{0004}a"[|r0|];
}
method {:test} Test50() {
var r0 := LongestCommonPrefix("a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa", "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a");
expect |r0| <= |"a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa"| && r0 == "a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa"[0 .. |r0|] && |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a"[0 .. |r0|];
expect |r0| == |"a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa"| || |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a"| || "a\0aaa\U{0012}aaaaaaaa\U{0004}aaaa\U{0008}aaaaaaaaaaaaaaaa\naaaaa\U{0010}aaaaaa"[|r0|] != "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{000C}aaaa\U{000E}a"[|r0|];
}

// REPEAT 6 - TIME: 17.482465 s