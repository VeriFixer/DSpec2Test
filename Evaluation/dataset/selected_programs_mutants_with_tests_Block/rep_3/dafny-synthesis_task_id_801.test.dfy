
method {:test} Test5() {
var r0 := CountEqualNumbers(29, 30, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 30 && 30 == 30;
expect r0 == 2 <==> (29 == 30 && 30 != 30) || (29 != 30 && 30 == 30) || (29 == 30 && 30 != 30);
expect r0 == 1 <==> 29 != 30 && 30 != 30 && 29 != 30;
}
method {:test} Test6() {
var r0 := CountEqualNumbers(31, 31, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 31 == 31 && 31 == 31;
expect r0 == 2 <==> (31 == 31 && 31 != 31) || (31 != 31 && 31 == 31) || (31 == 31 && 31 != 31);
expect r0 == 1 <==> 31 != 31 && 31 != 31 && 31 != 31;
}

// REPEAT 3 - TIME: 5.5958199 s