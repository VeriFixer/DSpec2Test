
method {:test} Test26() {
expect |"\0aaa\U{0002}"| == |"\0aa??"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("\0aaa\U{0002}", "\0aa??");
expect r0 <==> forall n :: 0 <= n < |"\0aaa\U{0002}"| ==> "\0aaa\U{0002}"[n] == "\0aa??"[n] || "\0aa??"[n] == '?';
}
method {:test} Test27() {
expect |"aaaaa\U{0014}aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaa\0\U{000E}\U{0018}a"| == |"aaaaaaaaaaa\U{0010}\U{000C}aaaa\naaaaa\U{0008}aa\U{0012}aaaaa\U{0016}aaaaa\U{0002}\U{001A}a\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\U{0014}aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaa\0\U{000E}\U{0018}a", "aaaaaaaaaaa\U{0010}\U{000C}aaaa\naaaaa\U{0008}aa\U{0012}aaaaa\U{0016}aaaaa\U{0002}\U{001A}a\U{0004}");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\U{0014}aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaa\0\U{000E}\U{0018}a"| ==> "aaaaa\U{0014}aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaa\0\U{000E}\U{0018}a"[n] == "aaaaaaaaaaa\U{0010}\U{000C}aaaa\naaaaa\U{0008}aa\U{0012}aaaaa\U{0016}aaaaa\U{0002}\U{001A}a\U{0004}"[n] || "aaaaaaaaaaa\U{0010}\U{000C}aaaa\naaaaa\U{0008}aa\U{0012}aaaaa\U{0016}aaaaa\U{0002}\U{001A}a\U{0004}"[n] == '?';
}

// REPEAT 5 - TIME: 14.1525221 s