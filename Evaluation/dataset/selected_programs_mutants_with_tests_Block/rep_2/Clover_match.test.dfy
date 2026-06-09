
method {:test} Test3() {
expect |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}", "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}");
expect r0 <==> forall n :: 0 <= n < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"[n] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"[n] || "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}a\U{0002}"[n] == '?';
}
method {:test} Test4() {
expect |"a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0008}\U{0006}"| == |"a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0008}\U{0006}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0008}\U{0006}", "a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0008}\U{0006}");
expect r0 <==> forall n :: 0 <= n < |"a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0008}\U{0006}"| ==> "a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0008}\U{0006}"[n] == "a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0008}\U{0006}"[n] || "a\U{0002}aaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\na\U{0008}\U{0006}"[n] == '?';
}
method {:test} Test5() {
expect |"a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"| == |"a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Match("a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a", "a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a");
expect r0 <==> forall n :: 0 <= n < |"a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"| ==> "a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"[n] == "a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"[n] || "a\0aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0004}a"[n] == '?';
}

// REPEAT 2 - TIME: 4.3651174 s