
method {:test} Test2() {
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}99");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}99"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}99"[i] in "0123456789";
}

// REPEAT 3 - TIME: 3.1010396 s