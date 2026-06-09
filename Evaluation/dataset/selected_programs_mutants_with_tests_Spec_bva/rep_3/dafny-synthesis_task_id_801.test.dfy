
method {:test} Test55() {
var r0 := CountEqualNumbers(34, 34, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 34;
expect r0 == 2 <==> (34 == 34 && 34 != 34) || (34 != 34 && 34 == 34) || (34 == 34 && 34 != 34);
expect r0 == 1 <==> 34 != 34 && 34 != 34 && 34 != 34;
}
method {:test} Test56() {
var r0 := CountEqualNumbers(34, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 33 && 33 == 33;
expect r0 == 2 <==> (34 == 33 && 33 != 33) || (34 != 33 && 33 == 33) || (34 == 33 && 33 != 33);
expect r0 == 1 <==> 34 != 33 && 33 != 33 && 34 != 33;
}
method {:test} Test57() {
var r0 := CountEqualNumbers(34, 35, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 35 && 35 == 34;
expect r0 == 2 <==> (34 == 35 && 35 != 34) || (34 != 35 && 35 == 34) || (34 == 34 && 35 != 34);
expect r0 == 1 <==> 34 != 35 && 35 != 34 && 34 != 34;
}
method {:test} Test58() {
var r0 := CountEqualNumbers(34, 33, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 33 && 33 == 35;
expect r0 == 2 <==> (34 == 33 && 33 != 35) || (34 != 33 && 33 == 35) || (34 == 35 && 33 != 35);
expect r0 == 1 <==> 34 != 33 && 33 != 35 && 34 != 35;
}
method {:test} Test59() {
var r0 := CountEqualNumbers(34, 34, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 33;
expect r0 == 2 <==> (34 == 34 && 34 != 33) || (34 != 34 && 34 == 33) || (34 == 33 && 34 != 33);
expect r0 == 1 <==> 34 != 34 && 34 != 33 && 34 != 33;
}

// REPEAT 3 - TIME: 198.2260582 s