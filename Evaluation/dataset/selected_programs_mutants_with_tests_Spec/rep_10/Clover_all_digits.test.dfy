
method {:test} Test18() {
var r0 := allDigits("20");
expect r0 <==> forall i :: 0 <= i < |"20"| ==> "20"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\U{0004}\U{0002}aaaaaaaaaaaa\0aaaaaaaaaaaa\U{0006}\U{0008}\naaaaaaaa\U{000C}\U{000E}\U{0012}\U{0014}\U{0010}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}aaaaaaaaaaaa\0aaaaaaaaaaaa\U{0006}\U{0008}\naaaaaaaa\U{000C}\U{000E}\U{0012}\U{0014}\U{0010}"| ==> "\U{0004}\U{0002}aaaaaaaaaaaa\0aaaaaaaaaaaa\U{0006}\U{0008}\naaaaaaaa\U{000C}\U{000E}\U{0012}\U{0014}\U{0010}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 19.1073925 s