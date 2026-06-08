
method {:test} Test24() {
var r0 := LongestCommonPrefix("\0\U{0002}\U{0004}aa\U{0006}", "\0\U{0002}\U{0004}aa\U{0006}aa");
expect |r0| <= |"\0\U{0002}\U{0004}aa\U{0006}"| && r0 == "\0\U{0002}\U{0004}aa\U{0006}"[0 .. |r0|] && |r0| <= |"\0\U{0002}\U{0004}aa\U{0006}aa"| && r0 == "\0\U{0002}\U{0004}aa\U{0006}aa"[0 .. |r0|];
expect |r0| == |"\0\U{0002}\U{0004}aa\U{0006}"| || |r0| == |"\0\U{0002}\U{0004}aa\U{0006}aa"| || "\0\U{0002}\U{0004}aa\U{0006}"[|r0|] != "\0\U{0002}\U{0004}aa\U{0006}aa"[|r0|];
}
method {:test} Test25() {
var r0 := LongestCommonPrefix("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaa");
expect |r0| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa"[0 .. |r0|] && |r0| <= |"\U{0002}aaaaaaaaaaaaaaaa"| && r0 == "\U{0002}aaaaaaaaaaaaaaaa"[0 .. |r0|];
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa"| || |r0| == |"\U{0002}aaaaaaaaaaaaaaaa"| || "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaa"[|r0|] != "\U{0002}aaaaaaaaaaaaaaaa"[|r0|];
}
method {:test} Test26() {
var r0 := LongestCommonPrefix("a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a", "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a");
expect |r0| <= |"a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a"| && r0 == "a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a"[0 .. |r0|] && |r0| <= |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a"| && r0 == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a"[0 .. |r0|];
expect |r0| == |"a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a"| || |r0| == |"a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a"| || "a\0aaa\U{000C}a\U{0010}aaaaaaa\U{0008}aaaaaaaaaaaaa\U{0012}aaaaaaaaaaaa\U{000E}aa\U{0016}a"[|r0|] != "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}\naaaaaaaaaaaaaa\U{0014}aaaa\U{0004}a\U{0018}a"[|r0|];
}

// REPEAT 9 - TIME: 21.2492388 s