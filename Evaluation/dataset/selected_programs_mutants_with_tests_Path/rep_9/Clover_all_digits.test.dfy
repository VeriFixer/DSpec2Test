
method {:test} Test16() {
var r0 := allDigits("99a9aaaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaa9a99999");
expect r0 <==> forall i :: 0 <= i < |"99a9aaaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaa9a99999"| ==> "99a9aaaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaa9a99999"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\0aa\U{0002}aaaaaaaaaaaaaa\U{000C}\U{0004}aaaa\U{0008}aa\U{0006}aaaaaaaaaaa\U{000E}\U{0010}\n\U{0012}a");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaaaaa\U{000C}\U{0004}aaaa\U{0008}aa\U{0006}aaaaaaaaaaa\U{000E}\U{0010}\n\U{0012}a"| ==> "\0aa\U{0002}aaaaaaaaaaaaaa\U{000C}\U{0004}aaaa\U{0008}aa\U{0006}aaaaaaaaaaa\U{000E}\U{0010}\n\U{0012}a"[i] in "0123456789";
}

// REPEAT 9 - TIME: 83.2168299 s