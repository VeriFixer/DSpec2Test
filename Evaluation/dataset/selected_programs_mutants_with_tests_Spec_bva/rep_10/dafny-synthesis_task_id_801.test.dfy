
method {:test} Test90() {
var r0 := CountEqualNumbers(58, 58, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 58;
expect r0 == 2 <==> (58 == 58 && 58 != 58) || (58 != 58 && 58 == 58) || (58 == 58 && 58 != 58);
expect r0 == 1 <==> 58 != 58 && 58 != 58 && 58 != 58;
}
method {:test} Test91() {
var r0 := CountEqualNumbers(58, 59, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 59 && 59 == 59;
expect r0 == 2 <==> (58 == 59 && 59 != 59) || (58 != 59 && 59 == 59) || (58 == 59 && 59 != 59);
expect r0 == 1 <==> 58 != 59 && 59 != 59 && 58 != 59;
}
method {:test} Test92() {
var r0 := CountEqualNumbers(58, 59, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 59 && 59 == 58;
expect r0 == 2 <==> (58 == 59 && 59 != 58) || (58 != 59 && 59 == 58) || (58 == 58 && 59 != 58);
expect r0 == 1 <==> 58 != 59 && 59 != 58 && 58 != 58;
}
method {:test} Test93() {
var r0 := CountEqualNumbers(58, 60, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 60 && 60 == 59;
expect r0 == 2 <==> (58 == 60 && 60 != 59) || (58 != 60 && 60 == 59) || (58 == 59 && 60 != 59);
expect r0 == 1 <==> 58 != 60 && 60 != 59 && 58 != 59;
}
method {:test} Test94() {
var r0 := CountEqualNumbers(58, 58, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 59;
expect r0 == 2 <==> (58 == 58 && 58 != 59) || (58 != 58 && 58 == 59) || (58 == 59 && 58 != 59);
expect r0 == 1 <==> 58 != 58 && 58 != 59 && 58 != 59;
}

// REPEAT 10 - TIME: 262.5279267 s