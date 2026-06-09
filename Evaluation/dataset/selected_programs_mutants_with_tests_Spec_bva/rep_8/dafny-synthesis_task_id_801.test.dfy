
method {:test} Test80() {
var r0 := CountEqualNumbers(52, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 52;
expect r0 == 2 <==> (52 == 52 && 52 != 52) || (52 != 52 && 52 == 52) || (52 == 52 && 52 != 52);
expect r0 == 1 <==> 52 != 52 && 52 != 52 && 52 != 52;
}
method {:test} Test81() {
var r0 := CountEqualNumbers(53, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 52;
expect r0 == 2 <==> (53 == 52 && 52 != 52) || (53 != 52 && 52 == 52) || (53 == 52 && 52 != 52);
expect r0 == 1 <==> 53 != 52 && 52 != 52 && 53 != 52;
}
method {:test} Test82() {
var r0 := CountEqualNumbers(53, 52, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 53;
expect r0 == 2 <==> (53 == 52 && 52 != 53) || (53 != 52 && 52 == 53) || (53 == 53 && 52 != 53);
expect r0 == 1 <==> 53 != 52 && 52 != 53 && 53 != 53;
}
method {:test} Test83() {
var r0 := CountEqualNumbers(53, 52, 54);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 54;
expect r0 == 2 <==> (53 == 52 && 52 != 54) || (53 != 52 && 52 == 54) || (53 == 54 && 52 != 54);
expect r0 == 1 <==> 53 != 52 && 52 != 54 && 53 != 54;
}
method {:test} Test84() {
var r0 := CountEqualNumbers(52, 52, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 53;
expect r0 == 2 <==> (52 == 52 && 52 != 53) || (52 != 52 && 52 == 53) || (52 == 53 && 52 != 53);
expect r0 == 1 <==> 52 != 52 && 52 != 53 && 52 != 53;
}

// REPEAT 8 - TIME: 243.9024719 s