
method {:test} Test5() {
var r0 := CountEqualNumbers(29, 29, 29);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 29 && 29 == 29;
expect r0 == 2 <==> (29 == 29 && 29 != 29) || (29 != 29 && 29 == 29) || (29 == 29 && 29 != 29);
expect r0 == 1 <==> 29 != 29 && 29 != 29 && 29 != 29;
}
method {:test} Test6() {
var r0 := CountEqualNumbers(30, 31, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 31;
expect r0 == 2 <==> (30 == 31 && 31 != 31) || (30 != 31 && 31 == 31) || (30 == 31 && 31 != 31);
expect r0 == 1 <==> 30 != 31 && 31 != 31 && 30 != 31;
}
method {:test} Test7() {
var r0 := CountEqualNumbers(30, 31, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 30;
expect r0 == 2 <==> (30 == 31 && 31 != 30) || (30 != 31 && 31 == 30) || (30 == 30 && 31 != 30);
expect r0 == 1 <==> 30 != 31 && 31 != 30 && 30 != 30;
}
method {:test} Test8() {
var r0 := CountEqualNumbers(30, 31, 32);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 32;
expect r0 == 2 <==> (30 == 31 && 31 != 32) || (30 != 31 && 31 == 32) || (30 == 32 && 31 != 32);
expect r0 == 1 <==> 30 != 31 && 31 != 32 && 30 != 32;
}
method {:test} Test9() {
var r0 := CountEqualNumbers(30, 30, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 30 && 30 == 31;
expect r0 == 2 <==> (30 == 30 && 30 != 31) || (30 != 30 && 30 == 31) || (30 == 31 && 30 != 31);
expect r0 == 1 <==> 30 != 30 && 30 != 31 && 30 != 31;
}

// REPEAT 2 - TIME: 47.7074831 s