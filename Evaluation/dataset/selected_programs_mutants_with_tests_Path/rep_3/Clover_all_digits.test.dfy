
method {:test} Test4() {
var r0 := allDigits("1a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a");
expect r0 <==> forall i :: 0 <= i < |"1a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a"| ==> "1a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("aa\0");
expect r0 <==> forall i :: 0 <= i < |"aa\0"| ==> "aa\0"[i] in "0123456789";
}

// REPEAT 3 - TIME: 26.9360251 s