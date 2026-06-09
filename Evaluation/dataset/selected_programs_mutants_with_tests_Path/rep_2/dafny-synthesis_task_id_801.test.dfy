
method {:test} Test5() {
var r0 := CountEqualNumbers(28, 28, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 28 && 28 == 28;
expect r0 == 2 <==> (28 == 28 && 28 != 28) || (28 != 28 && 28 == 28) || (28 == 28 && 28 != 28);
expect r0 == 1 <==> 28 != 28 && 28 != 28 && 28 != 28;
}
method {:test} Test6() {
var r0 := CountEqualNumbers(28, 28, 29);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 28 && 28 == 29;
expect r0 == 2 <==> (28 == 28 && 28 != 29) || (28 != 28 && 28 == 29) || (28 == 29 && 28 != 29);
expect r0 == 1 <==> 28 != 28 && 28 != 29 && 28 != 29;
}
method {:test} Test7() {
var r0 := CountEqualNumbers(28, 27, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 27 && 27 == 28;
expect r0 == 2 <==> (28 == 27 && 27 != 28) || (28 != 27 && 27 == 28) || (28 == 28 && 27 != 28);
expect r0 == 1 <==> 28 != 27 && 27 != 28 && 28 != 28;
}
method {:test} Test8() {
var r0 := CountEqualNumbers(29, 27, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 27 && 27 == 27;
expect r0 == 2 <==> (29 == 27 && 27 != 27) || (29 != 27 && 27 == 27) || (29 == 27 && 27 != 27);
expect r0 == 1 <==> 29 != 27 && 27 != 27 && 29 != 27;
}
method {:test} Test9() {
var r0 := CountEqualNumbers(29, 27, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 27 && 27 == 28;
expect r0 == 2 <==> (29 == 27 && 27 != 28) || (29 != 27 && 27 == 28) || (29 == 28 && 27 != 28);
expect r0 == 1 <==> 29 != 27 && 27 != 28 && 29 != 28;
}

// REPEAT 2 - TIME: 9.8084815 s