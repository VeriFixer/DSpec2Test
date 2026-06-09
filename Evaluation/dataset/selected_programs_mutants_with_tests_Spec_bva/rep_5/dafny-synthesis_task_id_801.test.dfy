
method {:test} Test65() {
var r0 := CountEqualNumbers(41, 41, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 41 && 41 == 41;
expect r0 == 2 <==> (41 == 41 && 41 != 41) || (41 != 41 && 41 == 41) || (41 == 41 && 41 != 41);
expect r0 == 1 <==> 41 != 41 && 41 != 41 && 41 != 41;
}
method {:test} Test66() {
var r0 := CountEqualNumbers(43, 44, 44);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 44 && 44 == 44;
expect r0 == 2 <==> (43 == 44 && 44 != 44) || (43 != 44 && 44 == 44) || (43 == 44 && 44 != 44);
expect r0 == 1 <==> 43 != 44 && 44 != 44 && 43 != 44;
}
method {:test} Test67() {
var r0 := CountEqualNumbers(41, 42, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 42 && 42 == 41;
expect r0 == 2 <==> (41 == 42 && 42 != 41) || (41 != 42 && 42 == 41) || (41 == 41 && 42 != 41);
expect r0 == 1 <==> 41 != 42 && 42 != 41 && 41 != 41;
}
method {:test} Test68() {
var r0 := CountEqualNumbers(42, 43, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 43 && 43 == 41;
expect r0 == 2 <==> (42 == 43 && 43 != 41) || (42 != 43 && 43 == 41) || (42 == 41 && 43 != 41);
expect r0 == 1 <==> 42 != 43 && 43 != 41 && 42 != 41;
}
method {:test} Test69() {
var r0 := CountEqualNumbers(43, 43, 44);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 43 && 43 == 44;
expect r0 == 2 <==> (43 == 43 && 43 != 44) || (43 != 43 && 43 == 44) || (43 == 44 && 43 != 44);
expect r0 == 1 <==> 43 != 43 && 43 != 44 && 43 != 44;
}

// REPEAT 5 - TIME: 216.3652906 s