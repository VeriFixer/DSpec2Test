
method {:test} Test15() {
var r0 := CountEqualNumbers(33, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 33 && 33 == 33;
expect r0 == 2 <==> (33 == 33 && 33 != 33) || (33 != 33 && 33 == 33) || (33 == 33 && 33 != 33);
expect r0 == 1 <==> 33 != 33 && 33 != 33 && 33 != 33;
}
method {:test} Test16() {
var r0 := CountEqualNumbers(34, 34, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 33;
expect r0 == 2 <==> (34 == 34 && 34 != 33) || (34 != 34 && 34 == 33) || (34 == 33 && 34 != 33);
expect r0 == 1 <==> 34 != 34 && 34 != 33 && 34 != 33;
}
method {:test} Test17() {
var r0 := CountEqualNumbers(33, 34, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 34 && 34 == 33;
expect r0 == 2 <==> (33 == 34 && 34 != 33) || (33 != 34 && 34 == 33) || (33 == 33 && 34 != 33);
expect r0 == 1 <==> 33 != 34 && 34 != 33 && 33 != 33;
}
method {:test} Test18() {
var r0 := CountEqualNumbers(34, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 33 && 33 == 33;
expect r0 == 2 <==> (34 == 33 && 33 != 33) || (34 != 33 && 33 == 33) || (34 == 33 && 33 != 33);
expect r0 == 1 <==> 34 != 33 && 33 != 33 && 34 != 33;
}
method {:test} Test19() {
var r0 := CountEqualNumbers(35, 34, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 35 == 34 && 34 == 33;
expect r0 == 2 <==> (35 == 34 && 34 != 33) || (35 != 34 && 34 == 33) || (35 == 33 && 34 != 33);
expect r0 == 1 <==> 35 != 34 && 34 != 33 && 35 != 33;
}

// REPEAT 4 - TIME: 17.6327163 s