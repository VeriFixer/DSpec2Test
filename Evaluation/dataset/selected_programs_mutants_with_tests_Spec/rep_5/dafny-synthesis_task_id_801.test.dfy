
method {:test} Test20() {
var r0 := CountEqualNumbers(41, 41, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 41 && 41 == 41;
expect r0 == 2 <==> (41 == 41 && 41 != 41) || (41 != 41 && 41 == 41) || (41 == 41 && 41 != 41);
expect r0 == 1 <==> 41 != 41 && 41 != 41 && 41 != 41;
}
method {:test} Test21() {
var r0 := CountEqualNumbers(41, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 42 && 42 == 42;
expect r0 == 2 <==> (41 == 42 && 42 != 42) || (41 != 42 && 42 == 42) || (41 == 42 && 42 != 42);
expect r0 == 1 <==> 41 != 42 && 42 != 42 && 41 != 42;
}
method {:test} Test22() {
var r0 := CountEqualNumbers(41, 42, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 42 && 42 == 41;
expect r0 == 2 <==> (41 == 42 && 42 != 41) || (41 != 42 && 42 == 41) || (41 == 41 && 42 != 41);
expect r0 == 1 <==> 41 != 42 && 42 != 41 && 41 != 41;
}
method {:test} Test23() {
var r0 := CountEqualNumbers(42, 43, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 43 && 43 == 40;
expect r0 == 2 <==> (42 == 43 && 43 != 40) || (42 != 43 && 43 == 40) || (42 == 40 && 43 != 40);
expect r0 == 1 <==> 42 != 43 && 43 != 40 && 42 != 40;
}
method {:test} Test24() {
var r0 := CountEqualNumbers(40, 40, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 40 && 40 == 41;
expect r0 == 2 <==> (40 == 40 && 40 != 41) || (40 != 40 && 40 == 41) || (40 == 41 && 40 != 41);
expect r0 == 1 <==> 40 != 40 && 40 != 41 && 40 != 41;
}

// REPEAT 5 - TIME: 101.3716477 s