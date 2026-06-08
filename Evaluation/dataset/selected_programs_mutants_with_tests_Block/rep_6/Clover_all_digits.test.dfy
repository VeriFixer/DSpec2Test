
method {:test} Test5() {
var r0 := allDigits("8\U{0002}aaaaaaaaaaaa9");
expect r0 <==> forall i :: 0 <= i < |"8\U{0002}aaaaaaaaaaaa9"| ==> "8\U{0002}aaaaaaaaaaaa9"[i] in "0123456789";
}

// REPEAT 6 - TIME: 5.6530931 s