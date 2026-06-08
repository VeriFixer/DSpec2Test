
method {:test} Test30() {
var r0 := CountEqualNumbers(42, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 42 && 42 == 42;
expect r0 == 2 <==> (42 == 42 && 42 != 42) || (42 != 42 && 42 == 42) || (42 == 42 && 42 != 42);
expect r0 == 1 <==> 42 != 42 && 42 != 42 && 42 != 42;
}
method {:test} Test31() {
var r0 := CountEqualNumbers(43, 43, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 43 && 43 == 42;
expect r0 == 2 <==> (43 == 43 && 43 != 42) || (43 != 43 && 43 == 42) || (43 == 42 && 43 != 42);
expect r0 == 1 <==> 43 != 43 && 43 != 42 && 43 != 42;
}
method {:test} Test32() {
var r0 := CountEqualNumbers(42, 43, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 42 == 43 && 43 == 42;
expect r0 == 2 <==> (42 == 43 && 43 != 42) || (42 != 43 && 43 == 42) || (42 == 42 && 43 != 42);
expect r0 == 1 <==> 42 != 43 && 43 != 42 && 42 != 42;
}
method {:test} Test33() {
var r0 := CountEqualNumbers(43, 42, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 42 && 42 == 42;
expect r0 == 2 <==> (43 == 42 && 42 != 42) || (43 != 42 && 42 == 42) || (43 == 42 && 42 != 42);
expect r0 == 1 <==> 43 != 42 && 42 != 42 && 43 != 42;
}
method {:test} Test34() {
var r0 := CountEqualNumbers(44, 43, 42);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 44 == 43 && 43 == 42;
expect r0 == 2 <==> (44 == 43 && 43 != 42) || (44 != 43 && 43 == 42) || (44 == 42 && 43 != 42);
expect r0 == 1 <==> 44 != 43 && 43 != 42 && 44 != 42;
}

// REPEAT 7 - TIME: 49.4844567 s