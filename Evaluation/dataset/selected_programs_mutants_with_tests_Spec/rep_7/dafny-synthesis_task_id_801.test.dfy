
method {:test} Test30() {
var r0 := CountEqualNumbers(48, 48, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 48 && 48 == 48;
expect r0 == 2 <==> (48 == 48 && 48 != 48) || (48 != 48 && 48 == 48) || (48 == 48 && 48 != 48);
expect r0 == 1 <==> 48 != 48 && 48 != 48 && 48 != 48;
}
method {:test} Test31() {
var r0 := CountEqualNumbers(50, 51, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 51 && 51 == 51;
expect r0 == 2 <==> (50 == 51 && 51 != 51) || (50 != 51 && 51 == 51) || (50 == 51 && 51 != 51);
expect r0 == 1 <==> 50 != 51 && 51 != 51 && 50 != 51;
}
method {:test} Test32() {
var r0 := CountEqualNumbers(49, 48, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 48 && 48 == 49;
expect r0 == 2 <==> (49 == 48 && 48 != 49) || (49 != 48 && 48 == 49) || (49 == 49 && 48 != 49);
expect r0 == 1 <==> 49 != 48 && 48 != 49 && 49 != 49;
}
method {:test} Test33() {
var r0 := CountEqualNumbers(49, 48, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 48 && 48 == 50;
expect r0 == 2 <==> (49 == 48 && 48 != 50) || (49 != 48 && 48 == 50) || (49 == 50 && 48 != 50);
expect r0 == 1 <==> 49 != 48 && 48 != 50 && 49 != 50;
}
method {:test} Test34() {
var r0 := CountEqualNumbers(50, 50, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 50 && 50 == 51;
expect r0 == 2 <==> (50 == 50 && 50 != 51) || (50 != 50 && 50 == 51) || (50 == 51 && 50 != 51);
expect r0 == 1 <==> 50 != 50 && 50 != 51 && 50 != 51;
}

// REPEAT 7 - TIME: 98.8314062 s