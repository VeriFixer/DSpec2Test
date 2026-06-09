
method {:test} Test10() {
var r0 := CountEqualNumbers(33, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 33 && 33 == 33;
expect r0 == 2 <==> (33 == 33 && 33 != 33) || (33 != 33 && 33 == 33) || (33 == 33 && 33 != 33);
expect r0 == 1 <==> 33 != 33 && 33 != 33 && 33 != 33;
}
method {:test} Test11() {
var r0 := CountEqualNumbers(34, 35, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 35 && 35 == 35;
expect r0 == 2 <==> (34 == 35 && 35 != 35) || (34 != 35 && 35 == 35) || (34 == 35 && 35 != 35);
expect r0 == 1 <==> 34 != 35 && 35 != 35 && 34 != 35;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(33, 24, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 24 && 24 == 33;
expect r0 == 2 <==> (33 == 24 && 24 != 33) || (33 != 24 && 24 == 33) || (33 == 33 && 24 != 33);
expect r0 == 1 <==> 33 != 24 && 24 != 33 && 33 != 33;
}
method {:test} Test13() {
var r0 := CountEqualNumbers(33, 24, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 24 && 24 == 34;
expect r0 == 2 <==> (33 == 24 && 24 != 34) || (33 != 24 && 24 == 34) || (33 == 34 && 24 != 34);
expect r0 == 1 <==> 33 != 24 && 24 != 34 && 33 != 34;
}
method {:test} Test14() {
var r0 := CountEqualNumbers(34, 34, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 35;
expect r0 == 2 <==> (34 == 34 && 34 != 35) || (34 != 34 && 34 == 35) || (34 == 35 && 34 != 35);
expect r0 == 1 <==> 34 != 34 && 34 != 35 && 34 != 35;
}

// REPEAT 3 - TIME: 69.7405027 s