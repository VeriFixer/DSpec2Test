
method {:test} Test21() {
var r0 := LongestCommonPrefix("\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa", "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}");
expect |r0| <= |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"| && r0 == "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"[0 .. |r0|] && |r0| <= |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"| && r0 == "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"[0 .. |r0|];
expect |r0| == |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"| || |r0| == |"\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"| || "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa"[|r0|] != "\U{0010}aaaaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0008}\naaaaaaaa\U{000C}\U{000E}aaaa\U{0002}aa\0a\U{0006}"[|r0|];
}
method {:test} Test22() {
var r0 := LongestCommonPrefix("\0aaaaa", "\0aa");
expect |r0| <= |"\0aaaaa"| && r0 == "\0aaaaa"[0 .. |r0|] && |r0| <= |"\0aa"| && r0 == "\0aa"[0 .. |r0|];
expect |r0| == |"\0aaaaa"| || |r0| == |"\0aa"| || "\0aaaaa"[|r0|] != "\0aa"[|r0|];
}
method {:test} Test23() {
var r0 := LongestCommonPrefix("\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}a");
expect |r0| <= |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 == "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[0 .. |r0|] && |r0| <= |"\0\U{0004}a"| && r0 == "\0\U{0004}a"[0 .. |r0|];
expect |r0| == |"\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| || |r0| == |"\0\U{0004}a"| || "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa"[|r0|] != "\0\U{0004}a"[|r0|];
}

// REPEAT 8 - TIME: 18.6683585 s