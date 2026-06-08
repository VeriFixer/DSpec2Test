
method {:test} Test17() {
var r0 := allDigits("13aaaaaa0aaaaaaaaaaaaaaaaaa2");
expect r0 <==> forall i :: 0 <= i < |"13aaaaaa0aaaaaaaaaaaaaaaaaa2"| ==> "13aaaaaa0aaaaaaaaaaaaaaaaaa2"[i] in "0123456789";
}
method {:test} Test18() {
var r0 := allDigits("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"[i] in "0123456789";
}

// REPEAT 3 - TIME: 11.7317724 s