
method {:test} Test12() {
expect |"aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"| == |"aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}", "aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"| ==> "aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"[n] == "aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"[n] || "aaaaaa\U{0002}a\U{0004}aaaaaa\U{000C}aa\U{0008}aaaaa\U{000E}aaaa\U{0010}\U{0006}aaaa\0aaaa\U{0012}\n\U{0014}"[n] == '?';
}
method {:test} Test13() {
expect |"aaaaaaaaaaaaaaaa\U{0012}aaaaaaaa\U{0006}aaaaaaaaaaa\n\0a\U{0014}"| == |"aaa\U{0004}aaa\U{000C}\U{0008}aaaaaa\U{000E}aaaaaaaaaa\U{0010}aaaaaaaaaaa\U{0002}\U{0016}\U{0018}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaaaaaaaaaaaaa\U{0012}aaaaaaaa\U{0006}aaaaaaaaaaa\n\0a\U{0014}", "aaa\U{0004}aaa\U{000C}\U{0008}aaaaaa\U{000E}aaaaaaaaaa\U{0010}aaaaaaaaaaa\U{0002}\U{0016}\U{0018}");
expect r0 <==> forall n :: 0 <= n < |"aaaaaaaaaaaaaaaa\U{0012}aaaaaaaa\U{0006}aaaaaaaaaaa\n\0a\U{0014}"| ==> "aaaaaaaaaaaaaaaa\U{0012}aaaaaaaa\U{0006}aaaaaaaaaaa\n\0a\U{0014}"[n] == "aaa\U{0004}aaa\U{000C}\U{0008}aaaaaa\U{000E}aaaaaaaaaa\U{0010}aaaaaaaaaaa\U{0002}\U{0016}\U{0018}"[n] || "aaa\U{0004}aaa\U{000C}\U{0008}aaaaaa\U{000E}aaaaaaaaaa\U{0010}aaaaaaaaaaa\U{0002}\U{0016}\U{0018}"[n] == '?';
}

// REPEAT 7 - TIME: 10.5344215 s