
method {:test} Test34() {
expect |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"| == |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a", "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"| ==> "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"[n] == "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"[n] || "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a"[n] == '?';
}
method {:test} Test35() {
expect |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}"| == |"aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}", "aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a");
expect r0 <==> forall n :: 0 <= n < |"aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}"| ==> "aaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{000E}\U{0006}"[n] == "aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a"[n] || "aaaaa\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa\n\U{0008}a"[n] == '?';
}

// REPEAT 9 - TIME: 17.7330449 s