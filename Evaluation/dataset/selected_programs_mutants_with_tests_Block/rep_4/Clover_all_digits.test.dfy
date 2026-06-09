
method {:test} Test3() {
var r0 := allDigits("0\U{0001}");
expect r0 <==> forall i :: 0 <= i < |"0\U{0001}"| ==> "0\U{0001}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 4.0420133 s