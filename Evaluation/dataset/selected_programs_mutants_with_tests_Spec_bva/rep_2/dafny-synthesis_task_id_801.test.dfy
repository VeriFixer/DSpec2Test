
method {:test} Test50() {
var r0 := CountEqualNumbers(24, 24, 24);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 24 == 24 && 24 == 24;
expect r0 == 2 <==> (24 == 24 && 24 != 24) || (24 != 24 && 24 == 24) || (24 == 24 && 24 != 24);
expect r0 == 1 <==> 24 != 24 && 24 != 24 && 24 != 24;
}
method {:test} Test51() {
var r0 := CountEqualNumbers(30, 31, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 31;
expect r0 == 2 <==> (30 == 31 && 31 != 31) || (30 != 31 && 31 == 31) || (30 == 31 && 31 != 31);
expect r0 == 1 <==> 30 != 31 && 31 != 31 && 30 != 31;
}
method {:test} Test52() {
var r0 := CountEqualNumbers(30, 31, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 30;
expect r0 == 2 <==> (30 == 31 && 31 != 30) || (30 != 31 && 31 == 30) || (30 == 30 && 31 != 30);
expect r0 == 1 <==> 30 != 31 && 31 != 30 && 30 != 30;
}
method {:test} Test53() {
var r0 := CountEqualNumbers(30, 31, 32);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 32;
expect r0 == 2 <==> (30 == 31 && 31 != 32) || (30 != 31 && 31 == 32) || (30 == 32 && 31 != 32);
expect r0 == 1 <==> 30 != 31 && 31 != 32 && 30 != 32;
}
method {:test} Test54() {
var r0 := CountEqualNumbers(24, 24, 29);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 24 == 24 && 24 == 29;
expect r0 == 2 <==> (24 == 24 && 24 != 29) || (24 != 24 && 24 == 29) || (24 == 29 && 24 != 29);
expect r0 == 1 <==> 24 != 24 && 24 != 29 && 24 != 29;
}

// REPEAT 2 - TIME: 189.2705381 s