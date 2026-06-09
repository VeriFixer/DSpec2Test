
method {:test} Test16() {
var r0 := CountEqualNumbers(41, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 42 && 42 == 42;
expect r0 == 2 <==> (41 == 42 && 42 != 42) || (41 != 42 && 42 == 42) || (41 == 42 && 42 != 42);
expect r0 == 1 <==> 41 != 42 && 42 != 42 && 41 != 42;
}
method {:test} Test17() {
var r0 := CountEqualNumbers(41, 41, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 41 == 41 && 41 == 41;
expect r0 == 2 <==> (41 == 41 && 41 != 41) || (41 != 41 && 41 == 41) || (41 == 41 && 41 != 41);
expect r0 == 1 <==> 41 != 41 && 41 != 41 && 41 != 41;
}

// REPEAT 8 - TIME: 11.2793461 s