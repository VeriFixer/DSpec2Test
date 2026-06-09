
method {:test} Test13() {
var r0 := CountEqualNumbers(40, 39, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 39 && 39 == 39;
expect r0 == 2 <==> (40 == 39 && 39 != 39) || (40 != 39 && 39 == 39) || (40 == 39 && 39 != 39);
expect r0 == 1 <==> 40 != 39 && 39 != 39 && 40 != 39;
}
method {:test} Test14() {
var r0 := CountEqualNumbers(40, 40, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 40 && 40 == 39;
expect r0 == 2 <==> (40 == 40 && 40 != 39) || (40 != 40 && 40 == 39) || (40 == 39 && 40 != 39);
expect r0 == 1 <==> 40 != 40 && 40 != 39 && 40 != 39;
}
method {:test} Test15() {
var r0 := CountEqualNumbers(39, 39, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 39 == 39 && 39 == 39;
expect r0 == 2 <==> (39 == 39 && 39 != 39) || (39 != 39 && 39 == 39) || (39 == 39 && 39 != 39);
expect r0 == 1 <==> 39 != 39 && 39 != 39 && 39 != 39;
}

// REPEAT 7 - TIME: 10.3525865 s