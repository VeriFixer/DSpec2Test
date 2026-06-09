
method {:test} Test75() {
var r0 := CountEqualNumbers(49, 49, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 49 && 49 == 49;
expect r0 == 2 <==> (49 == 49 && 49 != 49) || (49 != 49 && 49 == 49) || (49 == 49 && 49 != 49);
expect r0 == 1 <==> 49 != 49 && 49 != 49 && 49 != 49;
}
method {:test} Test76() {
var r0 := CountEqualNumbers(50, 49, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 49 && 49 == 49;
expect r0 == 2 <==> (50 == 49 && 49 != 49) || (50 != 49 && 49 == 49) || (50 == 49 && 49 != 49);
expect r0 == 1 <==> 50 != 49 && 49 != 49 && 50 != 49;
}
method {:test} Test77() {
var r0 := CountEqualNumbers(50, 49, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 49 && 49 == 50;
expect r0 == 2 <==> (50 == 49 && 49 != 50) || (50 != 49 && 49 == 50) || (50 == 50 && 49 != 50);
expect r0 == 1 <==> 50 != 49 && 49 != 50 && 50 != 50;
}
method {:test} Test78() {
var r0 := CountEqualNumbers(50, 49, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 49 && 49 == 51;
expect r0 == 2 <==> (50 == 49 && 49 != 51) || (50 != 49 && 49 == 51) || (50 == 51 && 49 != 51);
expect r0 == 1 <==> 50 != 49 && 49 != 51 && 50 != 51;
}
method {:test} Test79() {
var r0 := CountEqualNumbers(49, 49, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 49 && 49 == 50;
expect r0 == 2 <==> (49 == 49 && 49 != 50) || (49 != 49 && 49 == 50) || (49 == 50 && 49 != 50);
expect r0 == 1 <==> 49 != 49 && 49 != 50 && 49 != 50;
}

// REPEAT 7 - TIME: 234.7231327 s